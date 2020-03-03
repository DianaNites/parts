//! Error handling
use displaydoc::Display;
#[cfg(any(feature = "std", test))]
use thiserror::Error;

#[derive(Debug, Display)]
#[cfg_attr(any(feature = "std", test), derive(Error))]
pub enum Error {
    /// Not enough data was provided
    NotEnough,

    /// Encountered an unsupported GPT format
    Unsupported,

    /// The GPT Header was invalid: {0}
    Invalid(&'static str),
}

pub type Result<T> = core::result::Result<T, Error>;
