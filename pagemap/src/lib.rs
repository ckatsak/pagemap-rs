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

pub use error::{PageMapError, Result};
pub use kpage::KPageFlags;
pub use maps::{DeviceNumbers, MapsEntry, MemoryRegion, PagePermissions};
pub use crate::pagemap::{PageMap, PageMapEntry};

pub fn page_size() -> Result<u64> {
    match unsafe { libc::sysconf(libc::_SC_PAGESIZE) } {
        -1 => Err(std::io::Error::last_os_error().into()),
        sz => Ok(sz as u64),
    }
}
