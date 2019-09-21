//! Gpt Definitions
use crate::mbr::*;
use snafu::{ResultExt, Snafu};
use std::io::prelude::*;

#[derive(Debug, Snafu)]
pub struct GptError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid GPT Header: {}", source))]
    InvalidGptHeader { source: std::io::Error },

    #[snafu(display("{}", source))]
    MbrError { source: crate::mbr::MbrError },
}

type Result<T, E = GptError> = std::result::Result<T, E>;

#[derive(Debug, Default)]
struct GptHeader {
    // Hard-coded to "EFI PART"
    signature: String,

    // Currently hard-coded to `1.0`/`0x00010000`, but may change?
    revision: u32,

    // Must be header_size >= 92 and header_size <= logical block size
    header_size: u32,

    // CRC32(bytes[0..header_size])
    header_crc32: u32,

    // Must be zero
    _reserved: u32,

    // The logical block address we reside in
    this_lba: u64,

    // The logical block address the backup header is in
    alt_lba: u64,

    // Where partitions can start
    first_usable_lba: u64,

    // Where partitions must end
    last_usable_lba: u64,

    // Disk GUID
    disk_guid: u128,

    // Where our partition array starts on disk.
    partition_entries_lba: u64,

    // Number of partitions
    partition_len: u32,

    // Size of each partition entry structure
    // Must be 128 * 2^n, where n >= 0
    partition_entry_size: u32,

    // CRC32 of the partition array
    partitions_crc32: u32,
}

impl GptHeader {
    pub fn new() -> Self {
        unimplemented!()
    }
}

#[derive(Debug, Default)]
pub struct Gpt {
    mbr: ProtectiveMbr,
    header: GptHeader,
}

impl Gpt {
    pub fn new() -> Self {
        unimplemented!()
    }

    /// Read from an existing GPT Disk
    pub fn from_reader<RS>(mut source: RS) -> Result<Self>
    where
        RS: Read + Seek,
    {
        let mbr = ProtectiveMbr::from_reader(&mut source).context(MbrError)?;
        let header = GptHeader::new();
        Ok(Self {
            //
            mbr,
            header,
        })
    }

    pub fn from_bytes(_source: &[u8]) -> Result<Self> {
        unimplemented!()
    }

    pub fn from_file() -> Self {
        unimplemented!()
    }
}
