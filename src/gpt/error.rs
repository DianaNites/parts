//! Error handling
use displaydoc::Display;
#[cfg(feature = "std")]
use thiserror::Error;

/// Error type.
///
/// Note that this is non-exhaustive, the Io variant depends on `std`.
#[derive(Debug, Display)]
#[cfg_attr(feature = "std", derive(Error))]
#[non_exhaustive]
pub enum Error {
    /// I/O Error
    #[cfg(feature = "std")]
    Io(#[from] std::io::Error),

    /// Not enough data was provided
    ///
    /// Note that when using `std` methods it's likely that `Error::Io`
    /// will be returned rather than this.
    NotEnough,

    /// Encountered an unsupported GPT format
    Unsupported,

    /// The GPT Header was invalid: {0}
    Invalid(&'static str),

    /// Attempted to add overlapping partitions, or partition was out of usable
    /// range
    Overlap,
}

pub type Result<T> = core::result::Result<T, Error>;
