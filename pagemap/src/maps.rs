use std::fmt;

use bitflags::bitflags;

use crate::error::{PageMapError, Result};

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// MemoryRegion
//
///////////////////////////////////////////////////////////////////////////////////////////////////

/// A region of virtual memory, defined by the first and the next-to-last addresses that it
/// includes.
#[derive(Debug, Default, Clone, Copy)]
pub struct MemoryRegion {
    pub(crate) start: u64,
    pub(crate) end: u64,
}

impl MemoryRegion {
    /// Returns the first address included in the memory region.
    #[inline(always)]
    pub fn start_address(&self) -> u64 {
        self.start
    }

    /// Returns the last address included in the memory region.
    #[inline(always)]
    pub fn last_address(&self) -> u64 {
        self.end - 1
    }

    /// Returns the size of the memory region, in bytes.
    #[inline(always)]
    pub fn size(&self) -> u64 {
        self.end - self.start
    }
}

//impl std::convert::TryFrom<(u64, u64)> for MemoryRegion {
//    type Error = // TODO: Define own error types
//
//    fn try_from(r: (u64, u64)) -> Result<Self, Self::Error> {
//
//    }
//}

impl std::convert::From<(u64, u64)> for MemoryRegion {
    fn from(r: (u64, u64)) -> Self {
        debug_assert!(r.0 < r.1); // TODO: TryFrom
        MemoryRegion {
            start: r.0,
            end: r.1,
        }
    }
}

impl std::str::FromStr for MemoryRegion {
    type Err = PageMapError;

    fn from_str(s: &str) -> Result<Self> {
        let r: Vec<_> = s
            .splitn(2, '-')
            .map(|addr| u64::from_str_radix(addr, 16).map_err(PageMapError::ParseMemoryRegion))
            .collect::<Result<_>>()?;
        Ok((r[0], r[1]).into())
    }
}

impl fmt::Display for MemoryRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "0x{:016x}-0x{:016x} ({:5}K)",
            self.start,
            self.end,
            self.size() / 1024,
        )
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// PagePermissions
//
///////////////////////////////////////////////////////////////////////////////////////////////////

bitflags! {
    /// The permissions that a page may have.
    #[derive(Default)]
    pub struct PagePermissions: u8 {
        /// Permission to be read.
        const READ    = 1 << 0;
        /// Permission to be written.
        const WRITE   = 1 << 1;
        /// Permission to be executed.
        const EXECUTE = 1 << 2;
        /// A page can be `shared` or `private` (i.e., copy-on-write).
        const SHARED  = 1 << 3;
    }
}

impl std::str::FromStr for PagePermissions {
    type Err = PageMapError;

    // FIXME: This is a quick and dirty implementation, which would currently allow weird patterns,
    // like '----', 'wprx', etc.
    fn from_str(s: &str) -> Result<Self> {
        if s.len() != 4 {
            return Err(PageMapError::ParsePagePermissions(s.into()));
        }
        let mut ret: PagePermissions = Default::default();
        for c in s.chars() {
            ret |= match c {
                'r' => Self::READ,
                'w' => Self::WRITE,
                'x' => Self::EXECUTE,
                's' => Self::SHARED,
                'p' | '-' => Self::empty(),
                _ => return Err(PageMapError::ParsePagePermissions(s.into())),
            }
        }
        //if ret.is_empty() { Err(PageMapError::ParsePagePermissions(s.into())) } else { Ok(ret) }
        Ok(ret)
    }
}

impl fmt::Display for PagePermissions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = "---p".to_owned();
        if self.contains(Self::READ) {
            ret.replace_range(0..1, "r");
        }
        if self.contains(Self::WRITE) {
            ret.replace_range(1..2, "w");
        }
        if self.contains(Self::EXECUTE) {
            ret.replace_range(2..3, "x");
        }
        if self.contains(Self::SHARED) {
            ret.replace_range(3..4, "s");
        }
        write!(f, "{}", ret)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// DeviceNumbers
//
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Major and minor numbers of a file.
#[derive(Debug, Default, Clone, Copy)]
pub struct DeviceNumbers {
    major: u16, // major: u12
    minor: u32, // minor: u20
}

impl DeviceNumbers {
    /// Retrieve the major number.
    #[inline(always)]
    pub fn major(&self) -> u16 {
        self.major
    }

    /// Retrieve the minor number.
    #[inline(always)]
    pub fn minor(&self) -> u32 {
        self.minor
    }
}

impl std::convert::From<(u32, u32)> for DeviceNumbers {
    fn from(p: (u32, u32)) -> Self {
        debug_assert!(p.0 < 1 << 12); // TODO: TryFrom
        debug_assert!(p.1 < 1 << 20); // TODO: TryFrom
        DeviceNumbers {
            major: p.0 as u16,
            minor: p.1,
        }
    }
}

impl std::str::FromStr for DeviceNumbers {
    type Err = PageMapError;

    fn from_str(s: &str) -> Result<Self> {
        let p: Vec<_> = s
            .splitn(2, ':')
            .map(|addr| {
                u32::from_str_radix(addr, 16)
                    .map_err(|_| PageMapError::ParseDeviceNumbers(s.into()))
            })
            .collect::<Result<_>>()?;
        Ok((p[0], p[1]).into())
    }
}

impl fmt::Display for DeviceNumbers {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.major, self.minor)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// MapsEntry
//
///////////////////////////////////////////////////////////////////////////////////////////////////

/// An entry read from `/proc/<PID>/maps` for a process.
#[derive(Debug, Default, Clone)]
pub struct MapsEntry {
    /// The virtual memory region that the mapping concerns.
    pub(crate) region: MemoryRegion,
    /// The possible ways that pages in the memory region are allowed to be accessed.
    perms: PagePermissions,
    /// The offset in the file backing the mapping (if any) where the mapping begins.
    offset: u64,
    /// The major and minor numbers of the file backing the mapping, if any.
    dev: DeviceNumbers,
    /// The inode of the file backing the mapping, if any.
    inode: u64,
    /// The name of the file backing the mapping (if any), or a pseudo-path, as described in
    /// [`procfs(5)`].
    ///
    /// [`procfs(5)`]: https://man7.org/linux/man-pages/man5/proc.5.html
    pathname: Option<String>,
}

impl MapsEntry {
    /// Retrieve the virtual memory region of the mapping.
    #[inline(always)]
    pub fn memory_region(&self) -> MemoryRegion {
        self.region
    }

    /// Retrieve the permissions for the pages of the particular mapping, which dictate the
    /// possible ways that the pages of the mapping are allowed to be accessed.
    #[inline(always)]
    pub fn permissions(&self) -> PagePermissions {
        self.perms
    }

    /// Retrieve the offset in the file backing the mapping (if any) where the mapping begins.
    #[inline(always)]
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// Retrieve the major and minor numbers of the file backing the mapping, if any.
    #[inline(always)]
    pub fn device_numbers(&self) -> DeviceNumbers {
        self.dev
    }

    /// Retrieve the inode of the file backing the mapping, if any.
    #[inline(always)]
    pub fn inode(&self) -> u64 {
        self.inode
    }

    /// Retrieve the name of the file backing the mapping (if any), or a pseudo-path, as described
    /// in [`procfs(5)`].
    pub fn path(&self) -> Option<&str> {
        self.pathname.as_ref().map(|p| p.as_ref())
    }
}

impl std::str::FromStr for MapsEntry {
    type Err = PageMapError;

    fn from_str(s: &str) -> Result<Self> {
        let s: Vec<_> = s.split_ascii_whitespace().collect();
        Ok(MapsEntry {
            region: s[0].parse()?,
            perms: s[1].parse()?,
            offset: u64::from_str_radix(s[2], 16)?,
            dev: s[3].parse()?,
            inode: s[4].parse()?,
            pathname: s.get(5).map(|&p| p.to_owned()),
        })
    }
}

impl fmt::Display for MapsEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        write!(
            f,
            "{} {} {:20} {} {} {:?}",
            self.region, self.perms, self.offset, self.dev, self.inode, self.pathname
        )
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// tests
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_perms() {
        let perms = vec![
            "---s", "---p", "r--s", "r--p", "rw-s", "-w-s", "-w-p", "--xs", "--xp", "rw-p", "r-xp",
        ];
        for p in perms {
            eprint!("{:#?}  -->  ", p);
            let pp = p.parse::<PagePermissions>().unwrap();
            eprintln!("{:?}", pp);
            assert_eq!(format!("{}", pp), p);
        }
    }

    //#[test]
    ////#[should_panic]
    //fn test_invalid_perms() {
    //    assert!("----".parse::<PagePermissions>().is_err());
    //}

    #[test]
    fn test_maps_entry() -> anyhow::Result<()> {
        let start: u64 = u64::from_str_radix("7f368bc85000", 16).unwrap();
        eprintln!("start = {:#?}", start);

        let maps_entries = vec![
            "7f368bc85000-7f368bca7000 r--s 00000000 fe:00 400910                     /usr/share/zsh/functions/Completion/Base.zwc",
            "7f368bcaf000-7f368bcb3000 rw-p 00000000 00:00 0",
            "7f368bcc2000-7f368bcc3000 ---p 0000f000 fe:00 13377416                   /usr/lib/x86_64-linux-gnu/zsh/5.7.1/zsh/complist.so",
            "7ffcec729000-7ffcec784000 rw-p 00000000 00:00 0                          [stack]",
            "7ffcec7d1000-7ffcec7d3000 r-xp 00000000 00:00 0                          [vdso]",
        ];
        for line in maps_entries {
            eprintln!("line = {:#?}", line);
            let entry = line.parse::<MapsEntry>()?;
            eprintln!("entry = {:#?}", entry);
            eprintln!("pretty entry = {}\n", entry);
        }
        Ok(())
    }
}
