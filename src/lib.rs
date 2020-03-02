//! A Pure Rust library for working with GPT partition tables.
//!
//! This crate handles most, if not all, aspects of working with GPT for you.
//!
//! The primary type for interacting the a GPT table is [`Gpt`].
//! From here you can add and remove partitions.
//!
//! A Valid GPT partition consists of a MBR, and two GPT header/partition array
//! pairs.
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
//! use parts::{Gpt, GptPartBuilder, types::*};
//! use std::fs::File;
//!
//! const PATH: &str = "tests/data/test_parts";
//! // A reasonable-ish default size.
//! const BLOCK_SIZE: BlockSize = BlockSize(512);
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let mut gpt = Gpt::from_reader(File::open(PATH)?, BLOCK_SIZE)?;
//! let part = GptPartBuilder::new(BLOCK_SIZE)
//!     .name("Example")
//!     .size((BLOCK_SIZE * 2).into())
//!     .start(34.into())
//!     .finish();
//! gpt.add_partition(part);
//! #
//! # Ok(())
//! # }
//! ```
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![deny(missing_docs)]
#![cfg_attr(feature = "nightly", feature(doc_cfg))]
#![allow(dead_code)]

mod gpt;
mod mbr;
mod partitions;
pub mod types;

pub use gpt::*;
pub use partitions::*;
pub use uuid;
