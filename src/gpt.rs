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
    HeaderChecksumMismatch {},

    #[snafu(display("GPT Partitions Checksum Mismatch"))]
    PartitionsChecksumMismatch {},

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
#[derive(Default, Debug, Serialize, Deserialize, PartialEq)]
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
        ensure!(crc == old_crc, HeaderChecksumMismatch);
        self.header_crc32 = old_crc;
        //
        // TODO: Verify header::this_lba is correct
        //
        source
            .seek(SeekFrom::Start(self.partition_array_start * block_size))
            .context(Io)?;
        let mut buf: Vec<u8> = Vec::with_capacity((self.partitions * self.partition_size) as usize);
        buf.resize(buf.capacity(), 0);
        source.read_exact(&mut buf).context(Io)?;
        let crc = crc32::checksum_ieee(&buf);
        ensure!(crc == self.partitions_crc32, PartitionsChecksumMismatch);
        //
        Ok(())
    }

    pub(crate) fn to_writer<W: Write>(&self, mut dest: W, block_size: u64) -> Result<()> {
        bincode::serialize_into(&mut dest, self).context(Parse)?;
        // Account for reserved space.
        let len = (block_size - 92) as usize;
        let mut empty = Vec::with_capacity(len);
        empty.resize(len, 0u8);
        dest.write_all(&empty).context(Io)?;
        Ok(())
    }
}

/// A GPT Partition
#[derive(Default, Debug, Serialize, Deserialize, PartialEq)]
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

    pub(crate) fn to_writer<W: Write>(&self, dest: W) -> Result<()> {
        Ok(bincode::serialize_into(dest, self).context(Parse)?)
    }
}

/// A GPT Disk
#[derive(Debug, Default, PartialEq)]
pub struct Gpt {
    mbr: ProtectiveMbr,
    header: GptHeader,
    backup: GptHeader,
    partitions: Vec<GptPart>,

    /// The devices block size. ex, 512, 4096
    block_size: u64,
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
            block_size,
        })
    }

    pub fn from_file() -> Self {
        unimplemented!()
    }

    /// Write the GPT structure to a `Write`er.
    pub fn to_writer<W: Write + Seek>(&self, mut dest: W) -> Result<()> {
        self.mbr.to_writer(&mut dest).context(MbrError)?;

        self.header.to_writer(&mut dest, self.block_size)?;

        dest.seek(SeekFrom::Start(
            self.header.partition_array_start * self.block_size,
        ))
        .context(Io)?;
        for part in &self.partitions {
            part.to_writer(&mut dest)?;
        }

        dest.seek(SeekFrom::Start(self.header.alt_lba * self.block_size))
            .context(Io)?;
        self.backup.to_writer(&mut dest, self.block_size)?;

        dest.seek(SeekFrom::Start(
            self.backup.partition_array_start * self.block_size,
        ))
        .context(Io)?;
        for part in &self.partitions {
            part.to_writer(&mut dest)?;
        }

        //
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Gpt;
    use std::error::Error;
    use std::io::prelude::*;
    use std::io::Cursor;

    static TEST_PARTS: &str = "tests/data/test_parts";
    const BLOCK_SIZE: u64 = 512;
    const TEN_MIB_BYTES: usize = 10485760;

    type Result = std::result::Result<(), Box<dyn Error>>;

    // TODO: Refactor common code

    /// Tests that we can read an external GPT layout,
    /// serialize it, and deserialize it again, with it staying the same.
    #[test]
    fn gpt_roundtrip() -> Result {
        let mut file = std::fs::File::open(TEST_PARTS)?;
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf)?;
        //
        let src_gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE)?;
        //
        let mut buf = Cursor::new(Vec::with_capacity(TEN_MIB_BYTES));
        src_gpt.to_writer(&mut buf).unwrap();
        buf.set_position(0);
        //
        let new_gpt = Gpt::from_reader(&mut buf, BLOCK_SIZE)?;
        assert_eq!(src_gpt, new_gpt);
        //
        Ok(())
    }

    /// Tests that round-tripping gives us the exact bytes we got in
    #[test]
    fn exact_bytes() -> Result {
        let mut file = std::fs::File::open(TEST_PARTS)?;
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf)?;
        //
        let src_gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE)?;
        //
        let mut buf = Cursor::new(Vec::with_capacity(TEN_MIB_BYTES));
        src_gpt.to_writer(&mut buf).unwrap();
        //
        let v = buf.get_mut();
        assert_eq!(v.len(), TEN_MIB_BYTES);
        assert_eq!(v.len(), src_buf.len());
        assert_eq!(*v, src_buf);
        //
        Ok(())
    }
}
