//! parts
#![deny(missing_docs)]

mod gpt;
mod mbr;
pub mod partitions;

pub use gpt::*;
pub use uuid::Uuid;
