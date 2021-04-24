use std::io;

use thiserror::Error;

pub type Result<T> = std::result::Result<T, PageMapError>;

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

    /// Error retrieving `capabilities(7)`. Wrapper for [`CapsError`].
    ///
    /// [`CapsError`]: https://docs.rs/caps/0.5/caps/errors/struct.CapsError.html
    #[error(transparent)]
    CapsError(#[from] caps::errors::CapsError),

    /// Error parsing [`MemoryRegion`].
    ///
    /// [`MemoryRegion`]: struct.MemoryRegion.html
    #[error("could not parse MemoryRegion from the given addresses: {0}")]
    ParseMemoryRegion(std::num::ParseIntError),

    /// Error parsing [`PagePermissions`].
    ///
    /// [`PagePermissions`]: struct.PagePermissions.html
    #[error("could not parse valid PagePermissions from '{0}'")]
    ParsePagePermissions(String),

    /// Error parsing [`DeviceNumbers`].
    ///
    /// [`DeviceNumbers`]: struct.DeviceNumbers.html
    #[error("could not parse valid DeviceNumbers from '{0}'")]
    ParseDeviceNumbers(String),

    /// Generic integer parsing error.
    #[error(transparent)]
    ParseIntError(#[from] std::num::ParseIntError),
}
