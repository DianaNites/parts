//! Error handling
use displaydoc::Display;
#[cfg(any(feature = "std", test))]
use thiserror::Error;

/// Error type.
///
/// Note that this is non-exhaustive, the Io variant depends on `std`.
#[derive(Debug, Display)]
#[cfg_attr(any(feature = "std", test), derive(Error))]
#[non_exhaustive]
pub enum Error {
    /// I/O Error
    #[cfg(any(feature = "std", test))]
    Io(#[from] std::io::Error),

    /// Not enough data was provided
    NotEnough,

    /// Encountered an unsupported GPT format
    Unsupported,

    /// The GPT Header was invalid: {0}
    Invalid(&'static str),
}

pub type Result<T> = core::result::Result<T, Error>;
