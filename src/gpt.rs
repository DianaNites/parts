//! Gpt Definitions
use crate::{mbr::*, util::*};
use crc::crc32;
use serde::{Deserialize, Serialize};
use snafu::{ensure, ResultExt, Snafu};
use std::io::{prelude::*, SeekFrom};

#[derive(Debug, Snafu)]
pub struct GptError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid GPT Header Signature"))]
    Signature {},

    #[snafu(display("GPT Header Checksum Mismatch"))]
    ChecksumMismatch {},

    #[snafu(display("Error reading from device"))]
    Io { source: std::io::Error },

    #[snafu(display("Error parsing GPT Header structure"))]
    Parse { source: bincode::Error },

    #[snafu(display("{}", source))]
    MbrError { source: crate::mbr::MbrError },

    #[snafu(display("Invalid Block Size: Must be power of 2"))]
    BlockSize {},
}

type Result<T, E = GptError> = std::result::Result<T, E>;

/// The GPT Header Structure
#[derive(Default, Debug, Serialize, Deserialize)]
pub struct GptHeader {
    /// Hard-coded to "EFI PART"
    #[serde(with = "signature")]
    signature: String,

    /// Currently hard-coded to `1.0`/`0x00010000`, but may change?
    revision: u32,

    /// Must be header_size >= 92 and header_size <= logical block size
    header_size: u32,

    /// CRC32(bytes[0..header_size])
    header_crc32: u32,

    /// Must be zero
    _reserved: u32,

    /// The logical block address we reside in
    this_lba: u64,

    /// The logical block address the backup header is in
    alt_lba: u64,

    /// Where partitions can start
    first_usable_lba: u64,

    /// Where partitions must end
    last_usable_lba: u64,

    /// Disk GUID
    disk_guid: u128,

    /// Where our partition array starts on disk.
    partition_array_start: u64,

    /// Number of partitions
    partitions: u32,

    /// Size of each partition entry structure
    // Must be 128 * 2^n, where n >= 0
    partition_size: u32,

    /// CRC32 of the partition array
    partitions_crc32: u32,
}

impl GptHeader {
    /// Read the GPT Header from a `Read`er.
    ///
    /// The `Read`ers current position is undefined after this call.
    ///
    /// `block_size` is the device's logical block size.
    pub(crate) fn from_reader<R: Read + Seek>(mut source: R, block_size: u64) -> Result<Self> {
        let mut obj: GptHeader = bincode::deserialize_from(&mut source).context(Parse)?;
        obj.check_validity(source, block_size)?;
        Ok(obj)
    }

    /// Checks the validity of the header
    ///
    /// # Errors
    ///
    /// The position of `source` is undefined on error.
    /// If it's important, save it.
    ///
    /// # Details
    ///
    /// Checks the Signature, header CRC, and partition array CRC.
    fn check_validity<R: Read + Seek>(
        &mut self,
        mut source: R,
        block_size: u64,
    ) -> Result<(), InnerError> {
        ensure!(&self.signature == "EFI PART", Signature);
        let old_crc = std::mem::replace(&mut self.header_crc32, 0);
        // Relies on serialization being correct.
        let source_bytes = bincode::serialize(&self).context(Parse)?;
        let crc = crc32::checksum_ieee(&source_bytes[..self.header_size as usize]);
        ensure!(crc == old_crc, ChecksumMismatch);
        self.header_crc32 = old_crc;
        //
        // TODO: Verify header::this_lba is correct
        //
        // TODO: Support more block sizes
        source
            .seek(SeekFrom::Start(self.partition_array_start * block_size))
            .context(Io)?;
        let mut buf: Vec<u8> = Vec::with_capacity((self.partitions * self.partition_size) as usize);
        buf.resize(buf.capacity(), 0);
        source.read_exact(&mut buf).context(Io)?;
        let crc = crc32::checksum_ieee(&buf);
        ensure!(crc == self.partitions_crc32, ChecksumMismatch);
        //
        Ok(())
    }
}

/// A GPT Partition
#[derive(Default, Debug, Serialize, Deserialize)]
pub struct GptPart {
    /// Defines the type of this partition
    partition_type_guid: u128,

    /// Unique identifer for this partition
    partition_guid: u128,

    /// Where it starts on disk
    starting_lba: u64,

    /// Where it ends on disk
    ending_lba: u64,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Null-terminated name, UCS-2 string,
    /// max length of 36 including null.
    #[serde(with = "partition_name")]
    name: String,
}

impl GptPart {
    /// Reads a GPT Partition from a `Read`er.
    ///
    /// This will advance the reader by the size of a single partition entry.
    ///
    /// `size_of` is `GptHeader::partition_size`
    pub(crate) fn from_reader<R: Read + Seek>(mut source: R, size_of: u32) -> Result<Self> {
        let obj = bincode::deserialize_from(&mut source).context(Parse)?;
        // Seek past the remaining block.
        source
            .seek(SeekFrom::Current(size_of as i64 - 128))
            .context(Io)?;
        Ok(obj)
    }
}

/// A GPT Disk
#[derive(Debug, Default)]
pub struct Gpt {
    mbr: ProtectiveMbr,
    header: GptHeader,
    backup: GptHeader,
    partitions: Vec<GptPart>,
}

impl Gpt {
    /// Read from an existing GPT Disk
    ///
    /// `block_size` is the devices logical block size. ex: 512, 4096
    pub fn from_reader<RS>(mut source: RS, block_size: u64) -> Result<Self>
    where
        RS: Read + Seek,
    {
        if !block_size.is_power_of_two() {
            return BlockSize.fail().map_err(|e| e.into());
        }
        let mbr = ProtectiveMbr::from_reader(&mut source, block_size).context(MbrError)?;
        let header = GptHeader::from_reader(&mut source, block_size)?;
        let mut partitions = Vec::with_capacity(header.partitions as usize);
        source
            .seek(SeekFrom::Start(header.partition_array_start * block_size))
            .context(Io)?;
        for _ in 0..header.partitions {
            let part = GptPart::from_reader(&mut source, header.partition_size)?;
            // Ignore unused partitions, so partitions isn't cluttered.
            if part.partition_type_guid != 0 {
                partitions.push(part);
            }
        }
        // TODO: Properly handle primary and backup header.
        // Read the backup
        source
            .seek(SeekFrom::Start(header.alt_lba * block_size))
            .context(Io)?;
        //
        let backup = GptHeader::from_reader(&mut source, block_size)?;

        //
        Ok(Self {
            //
            mbr,
            header,
            backup,
            partitions,
        })
    }

    pub fn from_file() -> Self {
        unimplemented!()
    }
}
