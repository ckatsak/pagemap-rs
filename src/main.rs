//#![allow(unused_variables)] // FIXME

use std::fmt;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom};
////use std::path::PathBuf;

use bitflags::bitflags;

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
        debug_assert!(r.0 < r.1); // TODO: TryFrom
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
        let mut ret = "---p".to_owned();
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
        if ret == Self::EMPTY {
            panic!("invalid page permissions: '----'")
        }
        Ok(ret)
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

#[derive(Debug, Default, Clone)]
pub struct MapsEntry {
    region: MemoryRegion,
    perms: PagePermissions,
    offset: u64, // FIXME?
    dev: DeviceNumbers,
    inode: u64,
    pathname: Option<String>,
}

impl std::str::FromStr for MapsEntry {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
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
// PageMapData
//
///////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Copy)]
pub struct PageMapData(u64);

impl std::convert::From<u64> for PageMapData {
    fn from(v: u64) -> Self {
        PageMapData(v)
    }
}

impl PageMapData {
    pub fn raw(&self) -> u64 {
        self.0
    }

    pub fn present(&self) -> bool {
        self.0 & 1 << 63 != 0
    }

    pub fn swapped(&self) -> bool {
        self.0 & 1 << 62 != 0
    }

    pub fn file_mapped(&self) -> bool {
        self.0 & 1 << 61 != 0
    }

    pub fn shared_anonymous(&self) -> bool {
        !self.file_mapped()
    }

    pub fn exclusively_mapped(&self) -> bool {
        self.0 & 1 << 56 != 0
    }

    pub fn soft_dirty(&self) -> bool {
        self.0 & 1 << 55 != 0
    }

    // FIXME: custom error types!
    pub fn pfn(&self) -> Result<u64, anyhow::Error> {
        if !self.present() {
            Err(anyhow::anyhow!("Page is not present in RAM"))
        } else {
            //Ok(self.0 & !(0x_ff80_u64 << 48))
            //Ok(self.0 & 0x_007f_ffff_ffff_ffff_u64)
            Ok(self.0 & ((1 << 55) - 1))
        }
    }

    // FIXME: custom error types!
    pub fn swap_type(&self) -> Result<u8, anyhow::Error> {
        if !self.swapped() {
            Err(anyhow::anyhow!("Page is not swapped"))
        } else {
            Ok((self.0 & 0x1fu64) as u8)
        }
    }

    // FIXME: custom error types!
    pub fn swap_offset(&self) -> Result<u64, anyhow::Error> {
        if !self.swapped() {
            Err(anyhow::anyhow!("Page is not swapped"))
        } else {
            //Ok((self.0 & (0x_00ff_ffff_ffff_ffe0_u64)) >> 5)
            Ok((self.0 & (0x_007f_ffff_ffff_ffe0_u64)) >> 5)
        }
    }
}

impl fmt::Display for PageMapData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.present(), self.swapped()) {
            (true, true) => {
                write!(f, "PAGE BOTH PRESENT AND SWAPPED!") // FIXME
            }
            (true, false) => {
                write!(
                    f,
                    "PageMapData{{ present: {}; swapped: {}; file_mapped: {}; exclusively_mapped: {}; soft_dirty: {}; pfn: {:x} }}",
                    self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
                    self.soft_dirty(), self.pfn().unwrap(), // Safe because self.present() == true
                )
            }
            (false, true) => {
                write!(
                    f,
                    "PageMapData{{ present: {}; swapped: {}; file_mapped: {}; exclusively_mapped: {}; soft_dirty: {}; swap_type: {}; swap_offset: {} }}",
                    self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
                    self.soft_dirty(), self.swap_type().unwrap(), self.swap_offset().unwrap(),
                    // Safe to unwrap because self.swapped() == true
                )
            }
            (false, false) => {
                write!(
                    f,
                    "PageMapData{{ present: {}; swapped: {}; file_mapped: {}; exclusively_mapped: {}; soft_dirty: {} }}",
                    self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
                    self.soft_dirty(),
                )
            }
        }
        //if self.present() && self.swapped() {
        //    // present = 1, swapped = 1
        //    write!(f, "PAGE BOTH PRESENT AND SWAPPED!") // FIXME
        //} else if self.present() {
        //    // present = 1, swapped = 0
        //    write!(
        //        f,
        //        "PageMapData{{ present: {}; swapped: {}; file-mapped: {}; exclusively-mapped: {}; soft_dirty: {}; pfn: {:x} }}",
        //        self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
        //        self.soft_dirty(), self.pfn().unwrap(), // Safe because self.present() == true
        //    )
        //} else if self.swapped() {
        //    // present = 0, swapped = 1
        //    write!(
        //        f,
        //        "PageMapData{{ present: {}; swapped: {}; file-mapped: {}; exclusively-mapped: {}; soft_dirty: {}; swap-type: {}; swap-offset: {} }}",
        //        self.present(), self.swapped(), self.file_mapped(), self.exclusively_mapped(),
        //        self.soft_dirty(), self.swap_type().unwrap(), self.swap_offset().unwrap(),
        //    )
        //} else {
        //    // present = 0, swapped = 0
        //    write!(
        //        f,
        //        "PageMapData{{ present: {}; swapped: {}; file-mapped: {}; exclusively-mapped: {}; soft_dirty: {} }}",
        //        self.present(),
        //        self.swapped(),
        //        self.file_mapped(),
        //        self.exclusively_mapped(),
        //        self.soft_dirty(),
        //    )
        //}
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
    pmf: BufReader<File>,
    page_size: u64,
}

impl PageMap {
    // FIXME: define custom error type to return
    pub fn new(pid: u64) -> anyhow::Result<Self> {
        Ok(PageMap {
            pid,
            mf: BufReader::new(File::open(format!("/proc/{}/maps", pid))?),
            pmf: BufReader::new(File::open(format!("/proc/{}/pagemap", pid))?),
            page_size: page_size(),
        })
    }

    pub fn pid(&self) -> u64 {
        self.pid
    }

    // FIXME?: define custom error type to return?
    pub fn maps(&mut self) -> Result<Vec<MapsEntry>, std::num::ParseIntError> {
        self.mf
            .by_ref()
            .lines()
            .map(|line| line.unwrap().parse::<MapsEntry>())
            .collect()
    }

    // FIXME: define custom error type to return
    pub fn pagemap_region(&mut self, region: &MemoryRegion) -> anyhow::Result<Vec<PageMapData>> {
        //eprintln!(
        //    "region = {}; count = {}",
        //    region,
        //    (region.start..region.end)
        //        .step_by(self.page_size as usize)
        //        .count()
        //);
        let mut buf = [0; 8];
        (region.start..region.end)
            .step_by(self.page_size as usize)
            .map(|addr: u64| -> Result<_, _> {
                let vpn = addr / self.page_size;
                self.pmf.seek(SeekFrom::Start(vpn * 8))?;
                self.pmf.read_exact(&mut buf)?;
                Ok(u64::from_ne_bytes(buf).into())
                //let ret = u64::from_ne_bytes(buf);
                //eprintln!("addr: {:016x}; vpn: {}, v: {:016x}", addr, vpn, ret);
                //let ret = ret.into();
                //eprintln!("page = {}\n", ret);
                //Ok(ret)
            })
            .collect::<Result<_, _>>()
    }

    // FIXME: define custom error type to return
    pub fn pagemap(&mut self) -> Result<Vec<(MapsEntry, Vec<PageMapData>)>, anyhow::Error> {
        self.maps()?
            .iter()
            .map(|map_entry| Ok((map_entry.clone(), self.pagemap_region(&map_entry.region)?)))
            .collect()
        //
        //self.maps()?
        //    .iter()
        //    .map(
        //        |map_entry| -> Result<(MapsEntry, Vec<PageMapData>), anyhow::Error> {
        //            Ok((map_entry.clone(), self.pagemap_region(&map_entry.region)?))
        //        },
        //    )
        //    .collect()
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//
// helper functions
//
///////////////////////////////////////////////////////////////////////////////////////////////////

pub fn page_size() -> u64 {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as u64 } // FIXME: error handling
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
    //// let page_size = page_size();

    //// let maps_path = PathBuf::from(format!("/proc/{}/maps", pid));
    //// let pagemap_path = PathBuf::from(format!("/proc/{}/pagemap", pid));

    //// let maps = BufReader::new(File::open(&maps_path)?);
    //// let pagemap = BufReader::new(File::open(&pagemap_path)?);

    //// //let maps_entries: Vec<MapsEntry> = maps
    //// //    .lines()
    //// //    .map(|line| line.unwrap().parse())
    //// //    .collect::<Result<_, _>>()?;
    //// //for (i, entry) in maps_entries.iter().enumerate() {
    //// //    eprintln!("{:4}: {}", i, entry);
    //// //}

    //// let mut pm = PageMap::new(pid)?;
    //// //let e1 = maps_entries
    //// //    .get(0)
    //// //    .ok_or_else(|| anyhow::anyhow!("maps_entries empty!"))?;
    //// ////let r1 = &e1.region;
    //// //let p = pm.pagemap(&e1.region)?;
    //// //eprintln!("p = {:x?}", p);

    //// let entries = maps
    ////     .lines()
    ////     //.flat_map(|line| pm.pagemap(line.unwrap().parse::<MapsEntry>()?.region))
    ////     .flat_map(|line| -> Result<_, anyhow::Error> {
    ////         let entry = line.unwrap().parse::<MapsEntry>()?;
    ////         let pgs = pm.pagemap_region(&entry.region)?;
    ////         //eprintln!("pgs = {:x?}", pgs);
    ////         Ok((entry, pgs))
    ////     })
    ////     //.flatten()
    ////     .collect::<Vec<(MapsEntry, Vec<PageMapData>)>>();
    //// //eprintln!("entries = {:#016x?}", entries);
    //// eprintln!("count = {}", entries.len());

    //// eprintln!(
    ////     "# present = {}",
    ////     //entries.iter().filter(|&p| p.present()).count()
    ////     entries
    ////         .iter()
    ////         .map(|(_, pmds)| pmds.iter().filter(|&pmd| pmd.present()).count())
    ////         .sum::<usize>()
    //// );
    //// eprintln!(
    ////     "# swapped = {}",
    ////     //entries.iter().filter(|&p| p.swapped()).count()
    ////     entries
    ////         .iter()
    ////         .map(|(_, pmds)| pmds.iter().filter(|&pmd| pmd.swapped()).count())
    ////         .sum::<usize>()
    //// );

    let mut pm = PageMap::new(pid)?;
    let entries = pm.pagemap()?;
    eprintln!("\n\n{:#?}\n", entries);

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
            let pp = p.parse::<PagePermissions>().unwrap();
            eprintln!("pp = {:?}", pp);
            assert_eq!(format!("{}", pp), p);
        }
    }

    #[test]
    #[should_panic]
    fn test_invalid_perms() {
        assert!("----".parse::<PagePermissions>().is_err());
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
