use std::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read, Seek, SeekFrom};

use bitflags::bitflags;
use caps::{CapSet, Capability};
use thiserror::Error;

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// PageMapError
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Error)]
pub enum PageMapError {
    /// Bit `PM_PRESENT` is not set.
    #[error("page is not present")]
    PageNotPresent,

    /// Bit `PM_SWAP` is not set.
    #[error("page is not swapped")]
    PageNotSwapped,

    /// Error opening a file.
    #[error("could not open '{path}': {source}")]
    Open { path: String, source: io::Error },

    /// Error reading from a file.
    #[error("could not read '{path}': {source}")]
    Read { path: String, source: io::Error },

    /// Error seeking in a file.
    #[error("could not seek in '{path}': {source}")]
    Seek { path: String, source: io::Error },

    /// Error accessing a file.
    #[error("could not access file '{0}'")]
    Access(String),

    /// Generic I/O error.
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),

    /// Error retrieving `capabilities(7)`.
    #[error(transparent)]
    CapsError(#[from] caps::errors::CapsError),

    /// Error parsing [`MemoryRegion`].
    #[error("could not parse MemoryRegion from the given addresses: {0}")]
    ParseMemoryRegion(std::num::ParseIntError),

    /// Error parsing [`PagePermissions`].
    #[error("could not parse valid PagePermissions from '{0}'")]
    ParsePagePermissions(String),

    /// Error parsing [`DeviceNumbers`].
    #[error("could not parse valid DeviceNumbers from '{0}'")]
    ParseDeviceNumbers(String),

    /// Generic integer parsing error.
    #[error(transparent)]
    ParseIntError(#[from] std::num::ParseIntError),
}

pub type Result<T> = std::result::Result<T, PageMapError>;

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// KPageFlags
//
///////////////////////////////////////////////////////////////////////////////////////////////////

bitflags! {
    /// kpageflags as defined in Linux, at `include/uapi/linux/kernel-page-flags.h`.
    pub struct KPageFlags: u64 {
        const KPF_LOCKED        = 1 << 0;
        const KPF_ERROR         = 1 << 1;
        const KPF_REFERENCED    = 1 << 2;
        const KPF_UPTODATE      = 1 << 3;
        const KPF_DIRTY         = 1 << 4;
        const KPF_LRU           = 1 << 5;
        const KPF_ACTIVE        = 1 << 6;
        const KPF_SLAB          = 1 << 7;
        const KPF_WRITEBACK     = 1 << 8;
        const KPF_RECLAIM       = 1 << 9;
        const KPF_BUDDY         = 1 << 10;

        const KPF_MMAP          = 1 << 11;
        const KPF_ANON          = 1 << 12;
        const KPF_SWAPCACHE     = 1 << 13;
        const KPF_SWAPBACKED    = 1 << 14;
        const KPF_COMPOUND_HEAD = 1 << 15;
        const KPF_COMPOUND_TAIL = 1 << 16;
        const KPF_HUGE          = 1 << 17;
        const KPF_UNEVICTABLE   = 1 << 18;
        const KPF_HWPOISON      = 1 << 19;
        const KPF_NOPAGE        = 1 << 20;

        const KPF_KSM           = 1 << 21;
        const KPF_THP           = 1 << 22;
        const KPF_OFFLINE       = 1 << 23;
        const KPF_ZERO_PAGE     = 1 << 24;
        const KPF_IDLE          = 1 << 25;
        const KPF_PGTABLE       = 1 << 26;
    }
}

impl std::convert::From<u64> for KPageFlags {
    fn from(v: u64) -> Self {
        KPageFlags::from_bits_truncate(v)
    }
}

macro_rules! fn_get_bit {
    ($fn:ident, $bit:ident) => {
        /// Returns `Some(true)` if the corresponding bit is set; `Some(false)` otherwise. It
        /// returns `None` if `/proc/kpageflags` could not be read for the page at hand.
        #[inline(always)]
        pub fn $fn(&self) -> Option<bool> {
            self.kpgfl.map(|v| v.contains(KPageFlags::$bit))
        }
    };
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// MemoryRegion
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Default, Clone, Copy)]
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
    pub fn last_address(&self) -> u64 {
        self.end - 1
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
    #[derive(Default)]
    pub struct PagePermissions: u8 {
        const READ    = 1 << 0;
        const WRITE   = 1 << 1;
        const EXECUTE = 1 << 2;
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

#[derive(Debug, Default, Clone, Copy)]
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

#[derive(Debug, Default, Clone)]
pub struct MapsEntry {
    region: MemoryRegion,
    perms: PagePermissions,
    offset: u64,
    dev: DeviceNumbers,
    inode: u64,
    pathname: Option<String>,
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
// PageMapEntry
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Copy)]
pub struct PageMapEntry {
    pgmap: u64,
    kpgcn: Option<u64>,
    kpgfl: Option<KPageFlags>,
}

impl std::convert::From<u64> for PageMapEntry {
    fn from(pgmap: u64) -> Self {
        PageMapEntry {
            pgmap,
            kpgcn: None,
            kpgfl: None,
        }
    }
}

// TODO: Where to use?
impl std::convert::From<(u64, u64, u64)> for PageMapEntry {
    fn from((pgmap, kpgcn, kpgfl): (u64, u64, u64)) -> Self {
        PageMapEntry {
            pgmap,
            kpgcn: Some(kpgcn),
            kpgfl: Some(kpgfl.into()),
        }
    }
}

impl PageMapEntry {
    ///////////////////////////////////////////////////////////////////////////////////////////
    // pagemap constants as defined in Linux, at `fs/proc/task_mmu.c`
    ///////////////////////////////////////////////////////////////////////////////////////////

    pub const PM_PFRAME_BITS: u64 = 55;
    pub const PM_PFRAME_MASK: u64 = (1 << Self::PM_PFRAME_BITS) - 1;
    pub const PM_SOFT_DIRTY: u64 = 55;
    pub const PM_MMAP_EXCLUSIVE: u64 = 56;
    pub const PM_FILE: u64 = 61;
    pub const PM_SWAP: u64 = 62;
    pub const PM_PRESENT: u64 = 63;

    ///////////////////////////////////////////////////////////////////////////////////////////
    // /proc/PID/pagemap
    ///////////////////////////////////////////////////////////////////////////////////////////

    /// The raw `u64` value as read from [`procfs(5)`][procfs].
    #[inline(always)]
    pub fn raw_pagemap(&self) -> u64 {
        self.pgmap
    }

    /// Returns `true` if the `PM_PRESENT` bit is set; `false` otherwise.
    #[inline(always)]
    pub fn present(&self) -> bool {
        self.pgmap >> Self::PM_PRESENT & 1 == 1
    }

    /// Returns `true` if the `PM_SWAP` bit is set; `false` otherwise.
    #[inline(always)]
    pub fn swapped(&self) -> bool {
        self.pgmap >> Self::PM_SWAP & 1 == 1
    }

    /// Returns `true` if the `PM_FILE` bit is set; `false` otherwise.
    #[inline(always)]
    pub fn file_mapped(&self) -> bool {
        self.pgmap >> Self::PM_FILE & 1 == 1
    }

    /// Returns `true` if the `PM_FILE` bit is clear; `false` otherwise.
    #[inline(always)]
    pub fn shared_anonymous(&self) -> bool {
        self.pgmap >> Self::PM_FILE & 1 == 0
    }

    /// Returns `true` if the `PM_MMAP_EXCLUSIVE` bit is set; `false` otherwise.
    #[inline(always)]
    pub fn exclusively_mapped(&self) -> bool {
        self.pgmap >> Self::PM_MMAP_EXCLUSIVE & 1 == 1
    }

    /// Returns `true` if the `PM_SOFT_DIRTY` bit is set; `false` otherwise.
    #[inline(always)]
    pub fn soft_dirty(&self) -> bool {
        self.pgmap >> Self::PM_SOFT_DIRTY & 1 == 1
    }

    /// Returns the page frame number (decoding bits 0-54) if the `PM_PRESENT` bit is set;
    /// otherwise returns an error.
    pub fn pfn(&self) -> Result<u64> {
        if !self.present() {
            Err(PageMapError::PageNotPresent)
        } else {
            Ok(self.pgmap & Self::PM_PFRAME_MASK)
        }
    }

    /// Returns the swap type (decoding bits 0-4) if the `PM_SWAP` bit is set; otherwise returns an
    /// error.
    pub fn swap_type(&self) -> Result<u8> {
        if !self.swapped() {
            Err(PageMapError::PageNotSwapped)
        } else {
            Ok((self.pgmap & 0x1fu64) as u8)
        }
    }

    /// Returns the swap offset (decoding bits 5-55) if the `PM_SWAP` bit is set; otherwise returns
    /// an error.
    pub fn swap_offset(&self) -> Result<u64> {
        if !self.swapped() {
            Err(PageMapError::PageNotSwapped)
        } else {
            Ok((self.pgmap & (0x_007f_ffff_ffff_ffe0_u64)) >> 5)
        }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////
    // /proc/kpagecount
    ///////////////////////////////////////////////////////////////////////////////////////////

    /// The raw `u64` value as read from [`procfs(5)`][procfs].
    #[inline(always)]
    pub fn kpagecount(&self) -> Option<u64> {
        self.kpgcn
    }

    ///////////////////////////////////////////////////////////////////////////////////////////
    // /proc/kpageflags
    ///////////////////////////////////////////////////////////////////////////////////////////

    #[inline(always)]
    pub fn kpageflags(&self) -> Option<KPageFlags> {
        self.kpgfl
    }

    /// The raw `u64` value as read from [`procfs(5)`][procfs].
    #[inline(always)]
    pub fn raw_kpageflags(&self) -> Option<u64> {
        self.kpgfl.map(|kpgfl| kpgfl.bits())
    }

    fn_get_bit!(locked, KPF_LOCKED);
    fn_get_bit!(error, KPF_ERROR);
    fn_get_bit!(referenced, KPF_REFERENCED);
    fn_get_bit!(uptodate, KPF_UPTODATE);
    fn_get_bit!(dirty, KPF_DIRTY);
    fn_get_bit!(lru, KPF_LRU);
    fn_get_bit!(active, KPF_ACTIVE);
    fn_get_bit!(slab, KPF_SLAB);
    fn_get_bit!(writeback, KPF_WRITEBACK);
    fn_get_bit!(reclaim, KPF_RECLAIM);
    fn_get_bit!(buddy, KPF_BUDDY);
    fn_get_bit!(mmap, KPF_MMAP);
    fn_get_bit!(anon, KPF_ANON);
    fn_get_bit!(swapcache, KPF_SWAPCACHE);
    fn_get_bit!(swapbacked, KPF_SWAPBACKED);
    fn_get_bit!(compound_head, KPF_COMPOUND_HEAD);
    fn_get_bit!(compound_tail, KPF_COMPOUND_TAIL);
    fn_get_bit!(huge, KPF_HUGE);
    fn_get_bit!(unevictable, KPF_UNEVICTABLE);
    fn_get_bit!(hwpoison, KPF_HWPOISON);
    fn_get_bit!(nopage, KPF_NOPAGE);
    fn_get_bit!(ksm, KPF_KSM);
    fn_get_bit!(thp, KPF_THP);
    fn_get_bit!(offline, KPF_OFFLINE);
    fn_get_bit!(zero_page, KPF_ZERO_PAGE);
    fn_get_bit!(idle, KPF_IDLE);
    fn_get_bit!(pgtable, KPF_PGTABLE);
}

impl fmt::Display for PageMapEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.present(), self.swapped()) {
            (true, true) => panic!("PAGE BOTH PRESENT AND SWAPPED!"), // FIXME
            (true, false) => {
                write!(
                    f,
                    "PageMapEntry{{ present: {}; swapped: {}; file_mapped: {}; exclusively_mapped: {}; soft_dirty: {}; pfn: 0x{:x} }}",
                    self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
                    self.soft_dirty(), self.pfn().unwrap(), // Safe because self.present() == true
                )
            }
            (false, true) => {
                write!(
                    f,
                    "PageMapEntry{{ present: {}; swapped: {}; file_mapped: {}; exclusively_mapped: {}; soft_dirty: {}; swap_type: {}; swap_offset: 0x{:x} }}",
                    self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
                    self.soft_dirty(), self.swap_type().unwrap(), self.swap_offset().unwrap(),
                    // Safe to unwrap because self.swapped() == true
                )
            }
            (false, false) => {
                write!(
                    f,
                    "PageMapEntry{{ present: {}; swapped: {}; file_mapped: {}; exclusively_mapped: {}; soft_dirty: {} }}",
                    self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
                    self.soft_dirty(),
                )
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// PageMap
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct PageMap {
    pid: u64,
    mf: BufReader<File>,
    pmf: File,
    kcf: Option<File>,
    kff: Option<File>,
    page_size: u64,
}

impl PageMap {
    const KPAGECOUNT: &'static str = "/proc/kpagecount";
    const KPAGEFLAGS: &'static str = "/proc/kpageflags";

    pub fn new(pid: u64) -> Result<Self> {
        let (kcf, kff) = if caps::has_cap(None, CapSet::Effective, Capability::CAP_SYS_ADMIN)? {
            (
                Some(
                    File::open(Self::KPAGECOUNT).map_err(|e| PageMapError::Open {
                        path: Self::KPAGECOUNT.into(),
                        source: e,
                    })?,
                ),
                Some(
                    File::open(Self::KPAGEFLAGS).map_err(|e| PageMapError::Open {
                        path: Self::KPAGEFLAGS.into(),
                        source: e,
                    })?,
                ),
            )
        } else {
            (None, None)
        };
        let (maps_path, pagemap_path) = (
            format!("/proc/{}/maps", pid),
            format!("/proc/{}/pagemap", pid),
        );
        Ok(PageMap {
            pid,
            mf: BufReader::with_capacity(
                1 << 14,
                File::open(&maps_path).map_err(|e| PageMapError::Open {
                    path: maps_path,
                    source: e,
                })?,
            ),
            pmf: File::open(&pagemap_path).map_err(|e| PageMapError::Open {
                path: pagemap_path,
                source: e,
            })?,
            kcf,
            kff,
            page_size: page_size()?,
        })
    }

    /// Returns the `PID` of the process that this `PageMap` refers.
    pub fn pid(&self) -> u64 {
        self.pid
    }

    pub fn maps(&mut self) -> Result<Vec<MapsEntry>> {
        let pid = self.pid;
        self.mf
            .by_ref()
            .lines()
            .map(|line| {
                line.map_err(|e| PageMapError::Read {
                    path: format!("/proc/{}/maps", pid),
                    source: e,
                })?
                .parse()
            })
            .collect()
    }

    pub fn pagemap_region(&mut self, region: &MemoryRegion) -> Result<Vec<PageMapEntry>> {
        let mut buf = [0; 8];
        (region.start..region.end)
            .step_by(self.page_size as usize)
            .map(|addr: u64| -> Result<_> {
                let vpn = addr / self.page_size;
                self.pmf
                    .seek(SeekFrom::Start(vpn * 8))
                    .map_err(|e| PageMapError::Seek {
                        path: format!("/proc/{}/pagemap", self.pid),
                        source: e,
                    })?;
                self.pmf
                    .read_exact(&mut buf)
                    .map_err(|e| PageMapError::Read {
                        path: format!("/proc/{}/pagemap", self.pid),
                        source: e,
                    })?;
                Ok(u64::from_ne_bytes(buf).into())
            })
            .collect::<Result<_>>()
    }

    pub fn pagemap(&mut self) -> Result<Vec<(MapsEntry, Vec<PageMapEntry>)>> {
        self.maps()?
            .into_iter()
            .map(|map_entry| {
                let mut pmes = self.pagemap_region(&map_entry.region)?;
                if caps::has_cap(None, CapSet::Effective, Capability::CAP_SYS_ADMIN)? {
                    for pme in &mut pmes {
                        if let Ok(pfn) = pme.pfn() {
                            pme.kpgcn = Some(self.kpagecount(pfn)?);
                            pme.kpgfl = Some(self.kpageflags(pfn)?);
                        }
                    }
                }
                Ok((map_entry, pmes))
            })
            .collect()
    }

    /// Attempt to read the number of times each page is mapped.
    ///
    /// # Errors (TODO)
    ///
    /// - `self.kcf` is `None`
    /// - seek failure
    /// - read failure
    pub fn kpagecount(&self, pfn: u64) -> Result<u64> {
        let mut buf = [0; 8];
        let mut kcf = self
            .kcf
            .as_ref()
            .ok_or_else(|| PageMapError::Access(Self::KPAGECOUNT.into()))?;
        kcf.seek(SeekFrom::Start(pfn * 8))
            .map_err(|e| PageMapError::Seek {
                path: Self::KPAGECOUNT.into(),
                source: e,
            })?;
        kcf.read_exact(&mut buf).map_err(|e| PageMapError::Read {
            path: Self::KPAGECOUNT.into(),
            source: e,
        })?;
        Ok(u64::from_ne_bytes(buf))
    }

    /// Attempt to read the set of flags for each page.
    ///
    /// # Errors (TODO)
    ///
    /// - `self.kcf` is `None`
    /// - seek failure
    /// - read failure
    pub fn kpageflags(&self, pfn: u64) -> Result<KPageFlags> {
        let mut buf = [0; 8];
        let mut kff = self
            .kff
            .as_ref()
            .ok_or_else(|| PageMapError::Access(Self::KPAGEFLAGS.into()))?;
        kff.seek(SeekFrom::Start(pfn * 8))
            .map_err(|e| PageMapError::Seek {
                path: Self::KPAGEFLAGS.into(),
                source: e,
            })?;
        kff.read_exact(&mut buf).map_err(|e| PageMapError::Read {
            path: Self::KPAGEFLAGS.into(),
            source: e,
        })?;
        Ok(KPageFlags::from_bits_truncate(u64::from_ne_bytes(buf)))
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// helper functions
//
///////////////////////////////////////////////////////////////////////////////////////////////////

pub fn page_size() -> Result<u64> {
    match unsafe { libc::sysconf(libc::_SC_PAGESIZE) } {
        -1 => Err(io::Error::last_os_error().into()),
        sz => Ok(sz as u64),
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// binary
//
///////////////////////////////////////////////////////////////////////////////////////////////////

fn parse_args() -> u64 {
    std::env::args().nth(1).unwrap().parse().unwrap() // FIXME
}

fn main() -> anyhow::Result<()> {
    let pid = parse_args();

    let mut pm = PageMap::new(pid)?;
    let entries = pm.pagemap()?;
    //eprintln!("\n\n{:#?}\n", entries);
    entries.iter().for_each(|e| {
        eprintln!("-> {}", e.0);
        e.1.iter().filter(|&pme| pme.present()).for_each(|pme| {
            eprintln!("\t- {}", pme);
        });
    });

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
