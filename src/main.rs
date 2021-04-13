#![allow(unused_variables)] // FIXME

use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

use bitflags::bitflags;

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// MemoryRegion
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Default)]
pub struct MemoryRegion {
    start: u64,
    end: u64,
}

impl MemoryRegion {
    #[inline(always)]
    pub fn start_address(&self) -> u64 {
        self.start
    }

    #[inline(always)]
    pub fn end_address(&self) -> u64 {
        self.end
    }

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
        assert!(r.0 < r.1); // TODO: TryFrom
        MemoryRegion {
            start: r.0,
            end: r.1,
        }
    }
}

impl std::str::FromStr for MemoryRegion {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let r: Vec<_> = s
            .splitn(2, '-')
            .map(|addr| u64::from_str_radix(addr, 16))
            .collect::<Result<_, _>>()?;
        Ok((r[0], r[1]).into())
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// PagePermissions
//
///////////////////////////////////////////////////////////////////////////////////////////////////

bitflags! {
    #[derive(Default)]
    pub struct PagePermissions: u8 {
        const EMPTY = 0; // FIXME?
        const READ = 1;
        const WRITE = 2;
        const EXECUTE = 4;
        const SHARED = 8;
        const PRIVATE = 16;
    }
}

impl fmt::Display for PagePermissions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = "----".to_owned();
        if *self != Self::EMPTY {
            if *self & Self::READ == Self::READ {
                ret.replace_range(0..1, "r");
            }
            if *self & Self::WRITE == Self::WRITE {
                ret.replace_range(1..2, "w");
            }
            if *self & Self::EXECUTE == Self::EXECUTE {
                ret.replace_range(2..3, "x");
            }
            if *self & Self::PRIVATE == Self::PRIVATE {
                ret.replace_range(3..4, "p");
            } else if *self & Self::SHARED == Self::SHARED {
                ret.replace_range(3..4, "s");
            }
        }
        write!(f, "{}", ret)
    }
}

impl std::str::FromStr for PagePermissions {
    // This implementation never returns an error; in case of failure it panics. We therefore use
    // std::num::ParseIntError to be effortlessly compatible with the FromStr implementation for
    // MapsEntry.
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut ret = Default::default();
        for c in s.chars() {
            ret |= match c {
                'r' => Self::READ,
                'w' => Self::WRITE,
                'x' => Self::EXECUTE,
                'p' => Self::PRIVATE,
                's' => Self::SHARED,
                '-' => Self::EMPTY,
                _ => panic!("invalid page permissions"),
            }
        }
        Ok(ret)
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// DeviceNumbers
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Default)]
pub struct DeviceNumbers {
    major: u16, // major: u12
    minor: u32, // minor: u20
}

impl DeviceNumbers {
    #[inline(always)]
    pub fn major(&self) -> u16 {
        self.major
    }

    #[inline(always)]
    pub fn minor(&self) -> u32 {
        self.minor
    }
}

impl std::convert::From<(u32, u32)> for DeviceNumbers {
    fn from(p: (u32, u32)) -> Self {
        assert!(p.0 < 1 << 12); // TODO: TryFrom
        assert!(p.1 < 1 << 20); // TODO: TryFrom
        DeviceNumbers {
            major: p.0 as u16,
            minor: p.1,
        }
    }
}

impl std::str::FromStr for DeviceNumbers {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let p: Vec<_> = s
            .splitn(2, ':')
            .map(|addr| u32::from_str_radix(addr, 16))
            .collect::<Result<_, _>>()?;
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

#[derive(Debug, Default)]
struct MapsEntry {
    region: (u64, u64),
    perms: PagePermissions,
    offset: usize, // FIXME?
    dev: DeviceNumbers,
    inode: u64,
    pathname: Option<String>,
}

impl std::str::FromStr for MapsEntry {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s: Vec<_> = s.split_ascii_whitespace().collect();
        let region: Vec<_> = s[0]
            .splitn(2, '-')
            .map(|addr| u64::from_str_radix(addr, 16))
            .collect::<Result<_, _>>()?;

        Ok(MapsEntry {
            region: (region[0], region[1]),
            perms: s[1].parse()?,
            offset: usize::from_str_radix(s[2], 16)?,
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
            "{:?} {} {} {} {} {:?}",
            self.region, self.perms, self.offset, self.dev, self.inode, self.pathname
        )
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// helper functions
//
///////////////////////////////////////////////////////////////////////////////////////////////////

fn parse_args() -> u64 {
    std::env::args().nth(1).unwrap().parse().unwrap() // FIXME
}

fn page_size() -> usize {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize } // FIXME: error handling
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// core logic
//
///////////////////////////////////////////////////////////////////////////////////////////////////

fn main() -> anyhow::Result<()> {
    let pid = parse_args();
    let page_size = page_size();

    let maps_path = PathBuf::from(format!("/proc/{}/maps", pid));
    let pagemap_path = PathBuf::from(format!("/proc/{}/pagemap", pid));

    let maps = BufReader::new(File::open(&maps_path)?);
    let pagemap = BufReader::new(File::open(&pagemap_path)?);

    let entries: Vec<MapsEntry> = maps
        .lines()
        .map(|line| line.unwrap().parse())
        .collect::<Result<_, _>>()?;
    for (i, entry) in entries.iter().enumerate() {
        eprintln!("{:4}: {}", i, entry);
    }

    Ok(())
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
    fn test_perms() {
        let perms = vec![
            "----", "---s", "---p", "r--s", "r--p", "-w--", "-w-s", "-w-p", "--x-", "--xs", "--xp",
            "rw-p", "r-xp",
        ];
        for p in perms {
            let pp = p.parse::<PagePermissions>().unwrap();
            eprintln!("pp = {:?}", pp);
            assert_eq!(format!("{}", pp), p);
        }
    }

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
