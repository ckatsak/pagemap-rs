#![doc(html_root_url = "https://docs.rs/pagemap/0.1.0")]
#![warn(rust_2018_idioms)]
#![deny(
    //missing_docs,
    //missing_doc_code_examples, // nightly-only?
    unreachable_pub,
    broken_intra_doc_links,
)]

mod error;
#[macro_use]
mod kpage;
mod maps;
mod pagemap;

pub use crate::pagemap::{PageMap, PageMapEntry};
pub use error::{PageMapError, Result};
pub use kpage::KPageFlags;
pub use maps::{DeviceNumbers, MapsEntry, MemoryRegion, PagePermissions};

/// Retrieve system's page size in bytes.
pub fn page_size() -> Result<u64> {
    match unsafe { libc::sysconf(libc::_SC_PAGESIZE) } {
        -1 => Err(std::io::Error::last_os_error().into()),
        sz => Ok(sz as u64),
    }
}

/// Convenience function to retrieve the entries of `/proc/PID/maps` for a process.
#[inline]
pub fn maps(pid: u64) -> Result<Vec<MapsEntry>> {
    PageMap::new(pid)?.maps()
}

/// Convenience function to retrieve the entries of `/proc/PID/maps` for a process, combined with
/// those in `/proc/PID/pagemap` (and also `/proc/kpagecount` and `/proc/kpageflags` if
/// `CAP_SYS_ADMIN` is available).
#[inline]
pub fn pagemap(pid: u64) -> Result<Vec<(MapsEntry, Vec<PageMapEntry>)>> {
    PageMap::new(pid)?.pagemap()
}

/// Calculate the "unique set size (USS)" (i.e., the amount of memory that a process is using
/// which is not shared with any other process) in bytes.
pub fn uss(pid: u64) -> Result<u64> {
    Ok(PageMap::new(pid)?
        .pagemap()?
        .iter()
        .map(|(_, pmes)| {
            pmes.iter()
                .filter(|&pme| pme.present() && matches!(pme.kpagecount(), Some(c) if c == 1))
                .count() as u64
        })
        .sum::<u64>()
        * page_size()?)
}
