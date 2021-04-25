use std::io;

use thiserror::Error;

/// A custom `Result` type for this crate, combining a return value with a [`PageMapError`]. It is
/// used all over the crate and also returned by many functions and methods of its external API.
pub type Result<T> = std::result::Result<T, PageMapError>;

/// An error type returned by calls to the API exposed by this crate.
#[derive(Debug, Error)]
pub enum PageMapError {
    /// The [`PM_PRESENT`] bit is not set.
    ///
    /// [`PM_PRESENT`]: struct.PageMapEntry.html#associatedconstant.PM_PRESENT
    #[error("page is not present")]
    PageNotPresent,

    /// The [`PM_SWAP`] bit is not set.
    ///
    /// [`PM_SWAP`]: struct.PageMapEntry.html#associatedconstant.PM_SWAP
    #[error("page is not swapped")]
    PageNotSwapped,

    /// Error opening a file.
    #[error("could not open '{path}': {source}")]
    Open {
        /// The path of the file that was attempted to be opened.
        path: String,
        /// The underlying error.
        source: io::Error,
    },

    /// Error reading from a file.
    #[error("could not read '{path}': {source}")]
    Read {
        /// The path of the file that was attempted to be read.
        path: String,
        /// The underlying error.
        source: io::Error,
    },

    /// Error seeking in a file.
    #[error("could not seek in '{path}': {source}")]
    Seek {
        /// The path of the file that was attempted to be seeked.
        path: String,
        /// The underlying error.
        source: io::Error,
    },

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
