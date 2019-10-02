//! A Pure Rust library for working with GPT partition tables.
//!
//! This crate handles most, if not all, aspects of working with GPT for you.
//!
//! The primary type for interacting the a GPT table is [`Gpt`].
//! From here you can add and remove partitions.
//!
//! A Valid GPT partition consists of a MBR, and two GPT header/partition array pairs.
//!
//! This library will not accept invalid GPT partitions,
//! but does allow you to repair corrupt labels.
//!
//! Note that corrupt and invalid labels are not the same thing.
//!
//! Corrupt labels have an invalid primary OR backup header, but not both.
//!
//! # Usage
//!
//! Open a disk image file and add a partition.
//!
//! ```rust
//! use parts::{Gpt, GptPartBuilder};
//! use std::fs::File;
//!
//! static PATH: &str = "tests/data/test_parts";
//! // A reasonable-ish default size.
//! const BLOCK_SIZE: u64 = 512;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let mut gpt = Gpt::from_reader(File::open(PATH)?, BLOCK_SIZE)?;
//! let part = GptPartBuilder::new(BLOCK_SIZE)
//!     .name("Example")
//!     .size(BLOCK_SIZE * 2)
//!     .start(34)
//!     .finish();
//! gpt.add_partition(part);
//! #
//! # Ok(())
//! # }
//! ```
#![deny(missing_docs)]

mod gpt;
mod mbr;
#[doc(hidden)]
pub mod partitions;

pub use gpt::*;
pub use uuid;
