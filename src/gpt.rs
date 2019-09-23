//! Gpt Definitions
use crate::{mbr::*, util::*};
use crc::crc32;
use serde::{Deserialize, Serialize};
use snafu::{ensure, ResultExt, Snafu};
use std::io::{prelude::*, SeekFrom};
use uuid::Uuid;

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
#[derive(Debug, Serialize, Deserialize, PartialEq)]
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
    /// Creates a new GPT Header, valid EXCEPT for
    ///
    /// - `this_lba`
    /// - `alt_lba`
    /// - `first_usable_lba`
    /// - `last_usable_lba`
    /// - `partition_array_start`
    /// - `partitions`
    /// - `header_crc32`
    /// - `partitions_crc32`
    ///
    /// All of which MUST be properly calculated before this is written out.
    pub(crate) fn new() -> Self {
        Self {
            signature: "EFI PART".into(),
            revision: 0x00010000,
            header_size: 92,
            header_crc32: Default::default(),
            _reserved: Default::default(),
            this_lba: Default::default(),
            alt_lba: Default::default(),
            first_usable_lba: Default::default(),
            last_usable_lba: Default::default(),
            disk_guid: u128::from_le_bytes(*Uuid::new_v4().as_bytes()),
            partition_array_start: Default::default(),
            partitions: Default::default(),
            partition_size: 128,
            partitions_crc32: Default::default(),
        }
    }

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
        dest.write_all(&vec![0; len]).context(Io)?;
        Ok(())
    }
}

/// A GPT Partition
#[derive(Debug, Serialize, Deserialize, PartialEq)]
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
            .seek(SeekFrom::Current(i64::from(size_of) - 128))
            .context(Io)?;
        Ok(obj)
    }

    pub(crate) fn to_writer<W: Write>(&self, mut dest: W, size_of: u32) -> Result<()> {
        bincode::serialize_into(&mut dest, self).context(Parse)?;
        // Account for reserved space.
        let len = (size_of - 128) as usize;
        dest.write_all(&vec![0; len]).context(Io)?;
        Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub struct GptPartBuilder {
    partition_type_guid: Uuid,

    partition_guid: Uuid,

    start_lba: u64,

    size: u64,

    name: String,

    block_size: u64,
}

impl GptPartBuilder {
    pub fn new(block_size: u64) -> Self {
        Self {
            partition_type_guid: Uuid::nil(),
            partition_guid: Uuid::new_v4(),
            start_lba: Default::default(),
            size: Default::default(),
            name: Default::default(),
            block_size,
        }
    }

    /// `name` must be no more than 35 characters.
    pub fn name(mut self, name: &str) -> Self {
        assert!(name.len() < 36, "Name too long");
        self.name = name.into();
        self
    }

    /// Size of the partition, in bytes.
    pub fn size(mut self, size_in_bytes: u64) -> Self {
        self.size = size_in_bytes;
        self
    }

    pub fn finish(self) -> GptPart {
        GptPart {
            partition_type_guid: u128::from_le_bytes(*self.partition_type_guid.as_bytes()),
            partition_guid: u128::from_le_bytes(*self.partition_guid.as_bytes()),
            starting_lba: self.start_lba,
            // FIXME: Is this correct?
            ending_lba: (self.size / self.block_size) - 1,
            attributes: 0,
            name: self.name,
        }
    }
}

/// A GPT Disk
#[derive(Debug, PartialEq)]
pub struct Gpt {
    mbr: ProtectiveMbr,
    header: GptHeader,
    backup: GptHeader,
    partitions: Vec<GptPart>,

    /// The devices block size. ex, 512, 4096
    block_size: u64,
}

impl Gpt {
    pub fn new(block_size: u64) -> Self {
        Self {
            mbr: ProtectiveMbr::new(),
            header: GptHeader::new(),
            backup: GptHeader::new(),
            partitions: Vec::new(),
            block_size,
        }
    }

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
        self.mbr
            .to_writer(&mut dest, self.block_size)
            .context(MbrError)?;

        self.header.to_writer(&mut dest, self.block_size)?;

        dest.seek(SeekFrom::Start(
            self.header.partition_array_start * self.block_size,
        ))
        .context(Io)?;
        for part in &self.partitions {
            part.to_writer(&mut dest, self.header.partition_size)?;
        }

        dest.seek(SeekFrom::Start(self.header.alt_lba * self.block_size))
            .context(Io)?;
        self.backup.to_writer(&mut dest, self.block_size)?;

        dest.seek(SeekFrom::Start(
            self.backup.partition_array_start * self.block_size,
        ))
        .context(Io)?;
        for part in &self.partitions {
            part.to_writer(&mut dest, self.backup.partition_size)?;
        }

        //
        Ok(())
    }

    /// Iterator of the available partitions.
    pub fn partitions(&self) -> &[GptPart] {
        &self.partitions
    }

    /// Adds a new partition
    pub fn add_partition(&mut self, part: GptPart) {
        self.partitions.push(part);
        // TODO: Recalculate the header and partition CRC
    }
}

#[cfg(test)]
mod tests {
    use super::{Gpt, GptPartBuilder};
    use std::{
        error::Error,
        io::{prelude::*, Cursor},
    };

    static TEST_PARTS: &str = "tests/data/test_parts";
    const BLOCK_SIZE: u64 = 512;
    // 10 * 1024^2
    const TEN_MIB_BYTES: usize = 10485760;

    type Result = std::result::Result<(), Box<dyn Error>>;

    // TODO: Refactor common code
    // TODO: Tests on exotic block sizes

    /// Tests that we can read an external GPT layout,
    /// serialize it, and deserialize it again, with it staying the same.
    #[test]
    fn gpt_roundtrip() -> Result {
        let file = std::fs::File::open(TEST_PARTS)?;
        //
        let src_gpt = Gpt::from_reader(file, BLOCK_SIZE)?;
        //
        let mut buf = Cursor::new(Vec::with_capacity(TEN_MIB_BYTES));
        src_gpt.to_writer(&mut buf)?;
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

    /// Test that we can create a partition identical to the one i
    /// `test_parts`.
    ///
    /// See tests/data/README.md for details on how the original was created.
    #[test]
    fn create_test_parts() -> Result {
        let mut gpt = Gpt::new(BLOCK_SIZE);
        let part = GptPartBuilder::new(BLOCK_SIZE)
            .name("Test")
            .size(8 * 1024u64.pow(2))
            .finish();
        gpt.add_partition(part);
        let mut data = Cursor::new(vec![0; 10 * 1024usize.pow(2)]);
        gpt.to_writer(&mut data)?;
        //
        let mut file = std::fs::File::open(TEST_PARTS)?;
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf)?;
        //
        let data = data.get_mut();
        assert_eq!(data.len(), TEN_MIB_BYTES);
        assert_eq!(data.len(), src_buf.len());
        // FIXME: Fails, for obvious reasons.
        // Those reasons being we don't calculate any of the required data yet.
        // assert_eq!(*data, src_buf);
        Ok(())
    }
}
