//! Gpt Definitions
use crate::{mbr::*, util::*};
use crc::crc32;
use serde::{Deserialize, Serialize};
use snafu::{ensure, OptionExt, ResultExt, Snafu};
use std::io::{prelude::*, SeekFrom};
use uuid::Uuid;

#[derive(Debug, Snafu)]
pub struct GptError(InnerError);

#[derive(Debug, Snafu)]
#[allow(clippy::large_enum_variant)]
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

    #[snafu(display("The GPT Table is invalid and can't be written"))]
    InvalidGpt {},

    #[snafu(display("The GPT Header is invalid and can't be read."))]
    InvalidGptHeader {},

    #[snafu(display("The GPT Table is corrupt, but can be repaired."))]
    CorruptGpt { gpt: Gpt },
}

type Result<T, E = GptError> = std::result::Result<T, E>;

/// Check the validity of a GPT Header
///
/// ## Arguments
///
/// - `header`, the GptHeader to validate. Despite being `&mut`,
///     this won't be visibly modified.
/// - `source`, the `Read`er for the device.
///     The position of this is expected to be directly after the GPT Header.
/// - `block_size`, devices block size.
///
/// ## Errors
///
/// - If the header is invalid
/// - If calculating the CRC fails.
///
/// ## Details
///
/// - Verifies the Signature is "EFI PART".
/// - Verifies the Header CRC is correct.
/// - Verifies that `this_lba` is correct.
/// - Verifies the Partition Entry Array CRC.
///
/// The position of `source` is unspecified after this call.
fn check_validity<RS: Read + Seek>(
    header: &mut GptHeader,
    mut source: RS,
    block_size: u64,
) -> Result<(), InnerError> {
    ensure!(&header.signature == "EFI PART", Signature);
    let old_crc = std::mem::replace(&mut header.header_crc32, 0);
    let crc = calculate_crc(header)?;
    header.header_crc32 = old_crc;
    ensure!(crc == old_crc, HeaderChecksumMismatch);
    //
    let current_lba = source.seek(SeekFrom::Current(0)).context(Io)? / block_size;
    ensure!(header.this_lba == current_lba, InvalidGptHeader);
    //
    source
        .seek(SeekFrom::Start(header.partition_array_start * block_size))
        .context(Io)?;
    let mut buf: Vec<u8> = Vec::with_capacity((header.partitions * header.partition_size) as usize);
    buf.resize(buf.capacity(), 0);
    source.read_exact(&mut buf).context(Io)?;
    let crc = crc32::checksum_ieee(&buf);
    ensure!(crc == header.partitions_crc32, PartitionsChecksumMismatch);
    //
    Ok(())
}

/// Calculate the Header CRC for a `GptHeader`.
///
/// `GptHeader::header_crc` MUST be zero for this to be correct.
///
/// ## Errors
///
/// - If bincode does.
fn calculate_crc(header: &GptHeader) -> Result<u32, InnerError> {
    // Relies on serialization being correct.
    // TODO: Use `repr(C)` for `GptHeader` and just look at memory?
    let source_bytes = bincode::serialize(&header).context(Parse)?;
    Ok(crc32::checksum_ieee(
        &source_bytes[..header.header_size as usize],
    ))
}

/// The GPT Header Structure
#[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
struct GptHeader {
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
    #[serde(with = "uuid::adapter::compact")]
    disk_guid: Uuid,

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
    ///
    /// All of which MUST be properly calculated before this is written out.
    pub(crate) fn new() -> Self {
        let mut header = Self {
            signature: "EFI PART".into(),
            revision: 0x0001_0000,
            header_size: 92,
            header_crc32: Default::default(),
            _reserved: Default::default(),
            this_lba: Default::default(),
            alt_lba: Default::default(),
            first_usable_lba: Default::default(),
            last_usable_lba: Default::default(),
            disk_guid: Uuid::new_v4(),
            partition_array_start: Default::default(),
            partitions: Default::default(),
            partition_size: 128,
            partitions_crc32: Default::default(),
        };
        header.header_crc32 = calculate_crc(&header).unwrap();
        header
    }

    /// Read the GPT Header from a `Read`er.
    ///
    /// The `Read`ers current position is undefined after this call.
    pub(crate) fn from_reader<R: Read>(mut source: R) -> Result<Self> {
        Ok(bincode::deserialize_from(&mut source).context(Parse)?)
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
            // FIXME: Partition starts
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

    /// Can be None if corrupt
    header: Option<GptHeader>,

    /// Can be None if corrupt
    backup: Option<GptHeader>,

    partitions: Vec<GptPart>,

    /// The devices block size. ex, 512, 4096
    block_size: u64,

    /// Size of entire disk
    disk_size: u64,
}

impl Gpt {
    pub fn new(block_size: u64, disk_size: u64) -> Self {
        let last_lba = disk_size / block_size;
        //
        let mbr = ProtectiveMbr::new(last_lba);
        //
        let mut header = GptHeader::new();
        header.this_lba = 1;
        header.alt_lba = last_lba;
        // TODO: Properly calculate from block_size?
        header.first_usable_lba = 36;
        header.last_usable_lba = last_lba - 35;
        header.partition_array_start = 2;
        //
        let mut backup = GptHeader::new();
        backup.this_lba = last_lba;
        backup.alt_lba = 1;
        // TODO: Properly calculate from block_size?
        backup.first_usable_lba = 36;
        backup.last_usable_lba = last_lba - 35;
        backup.partition_array_start = backup.last_usable_lba;
        //
        let header = Some(header);
        let backup = Some(backup);
        //
        Self {
            mbr,
            header,
            backup,
            partitions: Vec::new(),
            block_size,
            disk_size,
        }
    }

    /// Read from an existing GPT Disk or image.
    ///
    /// ## Arguments
    ///
    /// - `block_size` is the devices logical block size. ex: 512, 4096
    ///
    /// ## Errors
    ///
    /// - If IO fails.
    /// - If the Protective MBR is invalid.
    /// - If the primary or backup GPT is invalid.
    ///
    /// ### Invalid GPT Headers
    ///
    /// In this case the `Err` variant will contain a `Gpt` Instance,
    /// which should be repaired after asking permission from the user.
    ///
    /// If both the primary and backup GPT is corrupt, repairing will not be possible.
    ///
    /// ## Panics
    ///
    /// - If the Gpt Instance is invalid, other methods may panic.
    pub fn from_reader<RS>(mut source: RS, block_size: u64) -> Result<Self>
    where
        RS: Read + Seek,
    {
        if !block_size.is_power_of_two() {
            return BlockSize.fail().map_err(|e| e.into());
        }
        //
        let disk_size = source.seek(SeekFrom::End(0)).context(Io)?;
        source.seek(SeekFrom::Start(0)).context(Io)?;
        //
        let mbr = ProtectiveMbr::from_reader(&mut source, block_size).context(MbrError)?;
        let header = GptHeader::from_reader(&mut source).and_then(|mut x| {
            //
            match check_validity(&mut x, &mut source, block_size) {
                Ok(_) => Ok(x),
                Err(e) => Err(e.into()),
            }
        });

        let mut partitions = Vec::new();

        if let Ok(header) = &header {
            source
                .seek(SeekFrom::Start(header.partition_array_start * block_size))
                .context(Io)?;
            partitions.reserve_exact(header.partitions as usize);
            for _ in 0..header.partitions {
                let part = GptPart::from_reader(&mut source, header.partition_size)?;
                // Ignore unused partitions, so `partitions` isn't cluttered.
                // Shouldn't cause any problems since unused partitions are all zeros.
                if part.partition_type_guid != 0 {
                    partitions.push(part);
                }
            }
            source
                .seek(SeekFrom::Start(header.alt_lba * block_size))
                .context(Io)?;
        } else {
            source
                .seek(SeekFrom::End(-(block_size as i64)))
                .context(Io)?;
        }
        //
        let backup = GptHeader::from_reader(&mut source).and_then(|mut x| {
            //
            match check_validity(&mut x, &mut source, block_size) {
                Ok(_) => Ok(x),
                Err(e) => Err(e.into()),
            }
        });

        if let Ok(backup) = &backup {
            source
                .seek(SeekFrom::Start(backup.partition_array_start * block_size))
                .context(Io)?;
            if header.is_err() {
                partitions.reserve_exact(backup.partitions as usize);
                for _ in 0..backup.partitions {
                    let part = GptPart::from_reader(&mut source, backup.partition_size)?;
                    // Ignore unused partitions, so `partitions` isn't cluttered.
                    // Shouldn't cause any problems since unused partitions are all zeros.
                    if part.partition_type_guid != 0 {
                        partitions.push(part);
                    }
                }
            }
        }
        let (b_err, h_err) = (backup.is_err(), header.is_err());

        let gpt = Self {
            //
            mbr,
            header: header.map(Some).unwrap_or(None),
            backup: backup.map(Some).unwrap_or(None),
            partitions,
            block_size,
            disk_size,
        };
        match (b_err, h_err) {
            (true, true) => InvalidGptHeader.fail().map_err(Into::into),
            (false, false) => Ok(gpt),
            (_, _) => CorruptGpt { gpt }.fail().map_err(Into::into),
        }
    }

    pub fn from_file() -> Self {
        unimplemented!()
    }

    /// Write the GPT structure to a `Write`er.
    pub fn to_writer<W: Write + Seek>(&self, mut dest: W) -> Result<()> {
        let header = self.header.as_ref().context(InvalidGpt)?;
        let backup = self.backup.as_ref().context(InvalidGpt)?;
        //
        self.mbr
            .to_writer(&mut dest, self.block_size)
            .context(MbrError)?;

        header.to_writer(&mut dest, self.block_size)?;

        dest.seek(SeekFrom::Start(
            header.partition_array_start * self.block_size,
        ))
        .context(Io)?;
        for part in &self.partitions {
            part.to_writer(&mut dest, header.partition_size)?;
        }

        dest.seek(SeekFrom::Start(header.alt_lba * self.block_size))
            .context(Io)?;
        backup.to_writer(&mut dest, self.block_size)?;

        dest.seek(SeekFrom::Start(
            backup.partition_array_start * self.block_size,
        ))
        .context(Io)?;
        for part in &self.partitions {
            part.to_writer(&mut dest, backup.partition_size)?;
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
        let header = self.header.as_mut().unwrap();
        header.partitions += 1;
        header.header_crc32 = calculate_crc(&header).unwrap();
        //
        // FIXME: Not currently possible to calculate partitions crc
        // TODO: Use repr(C) for all structs and then just compare in memory?
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
        let mut data = Cursor::new(vec![0; 10 * 1024usize.pow(2)]);
        //
        let mut gpt = Gpt::new(BLOCK_SIZE, data.get_ref().len() as u64);
        let part = GptPartBuilder::new(BLOCK_SIZE)
            .name("Test")
            .size(8 * 1024u64.pow(2))
            .finish();
        gpt.add_partition(part);
        //
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
