//! Gpt Definitions
use crate::mbr::*;
use crc::crc32;
use generic_array::{typenum::U36, GenericArray};
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

const EFI_PART: u64 = 0x5452_4150_2049_4645;
const MIN_PARTITIONS_BYTES: u64 = 16384;

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
    ensure!(header.signature == EFI_PART, Signature);
    ensure!(header.header_size >= 92, InvalidGptHeader);
    // FIXME: This one shouldn't be a requirement.
    ensure!(
        header.header_size <= std::mem::size_of::<GptHeader>() as u32,
        InvalidGptHeader
    );
    ensure!(header.header_size <= block_size as u32, InvalidGptHeader);
    let old_crc = std::mem::replace(&mut header.header_crc32, 0);
    let crc = calculate_crc(header);
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
fn calculate_crc(header: &GptHeader) -> u32 {
    let source_bytes = unsafe {
        std::slice::from_raw_parts(
            (header as *const _) as *const u8,
            std::mem::size_of::<GptHeader>(),
        )
    };
    crc32::checksum_ieee(
        // `GptHeader` has extra padding at the end, but it doesn't matter.
        &source_bytes[..header.header_size as usize],
    )
}

/// Changes the first 3 fields in a Uuid to little endian,
/// since GPT stores them weirdly.
///
/// This is an ugly hack.
// FIXME: An ugly hack for Uuid
// TODO: Just use a [u8; 16]?
fn uuid_hack(uuid: Uuid) -> Uuid {
    let (mut a, mut b, mut c, d) = uuid.as_fields();
    // `Uuid` gives them to us as big-endian, which Rust will interpret as little,
    // but they need to be little.
    //
    // use `swap_bytes` so that swapping doesn't depend on host endianness.
    //
    // `Uuid` will swap them again, so the final order is little.
    a = a.swap_bytes();
    b = b.swap_bytes();
    c = c.swap_bytes();
    Uuid::from_fields(a, b, c, d).unwrap()
}

/// The GPT Header Structure
#[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
#[repr(C)]
struct GptHeader {
    /// Hard-coded to "EFI PART",
    /// or the 64-bit constant 0x5452415020494645
    signature: u64,

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
    fn new() -> Self {
        Self {
            signature: EFI_PART,
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
        }
    }

    /// Read the GPT Header from a `Read`er.
    ///
    /// The `Read`ers current position is undefined after this call.
    fn from_reader<R: Read>(mut source: R) -> Result<Self> {
        Ok(bincode::deserialize_from(&mut source).context(Parse)?)
    }

    fn to_writer<W: Write>(&self, mut dest: W, block_size: u64) -> Result<()> {
        bincode::serialize_into(&mut dest, self).context(Parse)?;
        // Account for reserved space.
        let len = (block_size - 92) as usize;
        dest.write_all(&vec![0; len]).context(Io)?;
        Ok(())
    }
}

/// A GPT Partition
#[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
#[repr(C)]
pub struct GptPart {
    /// Defines the type of this partition
    #[serde(with = "uuid::adapter::compact")]
    partition_type_guid: Uuid,

    /// Unique identifer for this partition
    #[serde(with = "uuid::adapter::compact")]
    partition_guid: Uuid,

    /// Where it starts on disk
    starting_lba: u64,

    /// Where it ends on disk
    ending_lba: u64,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Null-terminated name, UCS-2/UTF-16LE string,
    name: GenericArray<u16, U36>,
}

impl GptPart {
    /// Reads a GPT Partition from a `Read`er.
    ///
    /// This will advance the reader by the size of a single partition entry.
    ///
    /// `size_of` is `GptHeader::partition_size`
    fn from_reader<R: Read + Seek>(mut source: R, size_of: u32) -> Result<Self> {
        let obj = bincode::deserialize_from(&mut source).context(Parse)?;
        // Seek past the remaining block.
        source
            .seek(SeekFrom::Current(i64::from(size_of) - 128))
            .context(Io)?;
        Ok(obj)
    }

    fn to_writer<W: Write>(&self, mut dest: W, size_of: u32) -> Result<()> {
        bincode::serialize_into(&mut dest, self).context(Parse)?;
        // Account for reserved space.
        let len = (size_of - 128) as usize;
        dest.write_all(&vec![0; len]).context(Io)?;
        Ok(())
    }

    /// Used by tests.
    #[allow(dead_code)]
    fn empty() -> Self {
        GptPart {
            partition_type_guid: Default::default(),
            partition_guid: Default::default(),
            starting_lba: Default::default(),
            ending_lba: Default::default(),
            attributes: Default::default(),
            name: Default::default(),
        }
    }
}

/// Builder struct for Gpt Partitions.
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
    /// Create a new Gpt Partition.
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
    ///
    /// ## Note
    ///
    /// Partitions can only be represented in logical block addresses,
    /// so this size should be divisible by the device block size.
    ///
    /// If it's not, the size will be rounded up.
    pub fn size(mut self, mut size_in_bytes: u64) -> Self {
        if size_in_bytes % self.block_size != 0 {
            size_in_bytes += self.block_size - (size_in_bytes % self.block_size)
        }
        self.size = size_in_bytes;
        self
    }

    /// Which Logical Block Address the partition should at start on disk.
    ///
    /// The ending LBA will be automatically calculated from
    /// the size of the partition and the its start.
    ///
    /// ## Examples
    ///
    /// Align at a 1MiB boundary
    ///
    /// ```rust
    /// # use parts::*;
    ///
    /// let block_size = 512;
    /// let part = GptPartBuilder::new(block_size).start(1024u64.pow(2) / block_size);
    /// ```
    pub fn start(mut self, lba: u64) -> Self {
        self.start_lba = lba;
        self
    }

    /// Set the partition GUID.
    ///
    /// ## Safety
    ///
    /// This is unsafe because GPT Partition GUID's are supposed to be unique.
    ///
    /// Having two partitions with the same GUID is a violation of the spec.
    pub unsafe fn part_guid(mut self, part_guid: Uuid) -> Self {
        self.partition_guid = uuid_hack(part_guid);
        self
    }

    /// Partition type GUID.
    // TODO: Known partition type constants.
    pub fn part_type(mut self, part_type: Uuid) -> Self {
        self.partition_type_guid = uuid_hack(part_type);
        self
    }

    /// Finalize the Gpt Partition.
    pub fn finish(self) -> GptPart {
        GptPart {
            partition_type_guid: self.partition_type_guid,
            partition_guid: self.partition_guid,
            starting_lba: self.start_lba,
            // inclusive on both ends.
            ending_lba: (self.start_lba + (self.size / self.block_size)) - 1,
            attributes: 0,
            name: self
                .name
                .encode_utf16()
                .chain([0].iter().copied().cycle())
                .take(36)
                .collect(),
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
        // logical block addresses start at zero.
        let last_lba = (disk_size / block_size) - 1;
        let min_partition_blocks = MIN_PARTITIONS_BYTES / block_size;
        //
        let mbr = ProtectiveMbr::new(last_lba);
        //
        let mut header = GptHeader::new();
        header.this_lba = 1;
        header.alt_lba = last_lba;
        // Plus two blocks, one for the MBR and one for the GPT Header.
        header.first_usable_lba = min_partition_blocks + 2;
        // Minus 1 block for the GPT Header
        header.last_usable_lba = last_lba - min_partition_blocks - 1;
        header.partition_array_start = 2;
        header.header_crc32 = calculate_crc(&header);
        //
        let mut backup: GptHeader = header.clone();
        backup.this_lba = last_lba;
        backup.alt_lba = 1;
        // usable addresses are not inclusive
        backup.partition_array_start = backup.last_usable_lba + 1;
        backup.header_crc32 = 0;
        backup.header_crc32 = calculate_crc(&backup);
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

    /// Set the disk GUID.
    ///
    /// ## Safety
    ///
    /// This is unsafe because GPT Disk GUID's are supposed to be unique.
    ///
    /// Having two disks with the same GUID is a violation of the spec.
    pub unsafe fn set_disk_guid(&mut self, new_guid: Uuid) {
        let new_guid = uuid_hack(new_guid);
        //
        self.header.as_mut().unwrap().disk_guid = new_guid;
        self.backup.as_mut().unwrap().disk_guid = new_guid;
        self.recalculate_crc();
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
                if part.partition_type_guid != Uuid::nil() {
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
                    if part.partition_type_guid != Uuid::nil() {
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
        //
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        header.partitions += 1;
        backup.partitions += 1;
        // FIXME: Support more partitions.
        // This would require moving the first usable lba forward, and the last usable one back.
        assert!(header.partitions <= 128, "Too many partitions");
        //
        self.recalculate_part_crc();
    }

    /// Recalculate the primary and backup header crc
    fn recalculate_crc(&mut self) {
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        header.header_crc32 = 0;
        header.header_crc32 = calculate_crc(&header);
        //
        backup.header_crc32 = 0;
        backup.header_crc32 = calculate_crc(&backup);
    }

    /// Recalculate the primary and backup partition crc.
    ///
    /// This also calls `recalculate_crc`, since updating the partition crc
    /// means the header one must be updated too.
    fn recalculate_part_crc(&mut self) {
        let source_bytes = unsafe {
            std::slice::from_raw_parts(
                self.partitions.as_ptr() as *const u8,
                std::mem::size_of::<GptPart>() * self.partitions.len(),
            )
        };
        let crc = crc32::checksum_ieee(&source_bytes);
        //
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        header.partitions_crc32 = crc;
        backup.partitions_crc32 = crc;
        //
        self.recalculate_crc();
    }
}

#[cfg(test)]
mod tests {
    use super::{Gpt, GptHeader, GptPart, GptPartBuilder};
    use prettydiff::basic::DiffOp;
    use prettydiff::diff_slice;
    use static_assertions::*;
    use std::{
        error::Error,
        io::{prelude::*, Cursor},
    };
    use uuid::Uuid;

    static TEST_PARTS: &str = "tests/data/test_parts";
    static TEST_PARTS_CF: &str = "tests/data/test_parts_cf";
    const BLOCK_SIZE: u64 = 512;
    // 10 * 1024^2
    const TEN_MIB_BYTES: usize = 10485760;

    const CF_DISK_GUID: &str = "A17875FB-1D86-EE4D-8DFE-E3E8ABBCD364";
    const CF_PART_GUID: &str = "97954376-2BB6-534B-A015-DF434A94ABA2";
    const LINUX_PART_GUID: &str = "0FC63DAF-8483-4772-8E79-3D69D8477DE4";

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

    /// Test that we can create a partition identical to the one in
    /// `test_parts_cf`.
    ///
    /// See tests/data/README.md for details on how the original was created.
    ///
    /// # Note
    ///
    /// GNU Parted has a ton of bugs, so this test isn't actually possible.
    ///
    /// In particular
    ///
    /// - Parted writes 0x000100 instead of 0x000200 for the starting CHS
    /// - Parted writes 0xFFFFFE instead of 0xFFFFFF for the ending CHS
    /// - Probably more.
    #[test]
    fn create_test_parts() -> Result {
        let mut data = Cursor::new(vec![0; TEN_MIB_BYTES]);
        //
        let mut gpt = Gpt::new(BLOCK_SIZE, data.get_ref().len() as u64);
        let mut part = GptPartBuilder::new(BLOCK_SIZE)
            .size(8 * 1024u64.pow(2))
            .start(1024u64.pow(2) / BLOCK_SIZE)
            .part_type(Uuid::parse_str(LINUX_PART_GUID)?);
        unsafe {
            part = part.part_guid(Uuid::parse_str(CF_PART_GUID)?);
        }
        let part = part.finish();
        //
        gpt.add_partition(part);
        unsafe {
            gpt.set_disk_guid(Uuid::parse_str(CF_DISK_GUID)?);
        };
        // NOTE: Cfdisk sets the first usable LBA to 2048
        // cfdisk also sets `partitions` to 128 all the time.
        // Ugly hack.
        gpt.header.as_mut().unwrap().first_usable_lba = 2048;
        gpt.backup.as_mut().unwrap().first_usable_lba = 2048;
        //
        gpt.header.as_mut().unwrap().partitions = 128;
        gpt.backup.as_mut().unwrap().partitions = 128;
        gpt.partitions.resize(128, GptPart::empty());
        //
        gpt.recalculate_part_crc();
        //
        gpt.to_writer(&mut data)?;
        //
        let mut file = std::fs::File::open(TEST_PARTS_CF)?;
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf)?;
        //
        let data = data.get_mut();
        assert_eq!(src_buf.len(), TEN_MIB_BYTES, "File too small");
        assert_eq!(data.len(), TEN_MIB_BYTES, "Too much being written");

        let block_size = BLOCK_SIZE as usize;
        let partition_entry_size = 128;
        // Just directly comparing the slices would generate FAR too much output.
        // This also highlights where the problem is, byte by byte, making debugging easier.
        let mbr_diff = diff_slice(&data[..block_size], &src_buf[..block_size]);
        let gpt_diff = diff_slice(
            &data[block_size..block_size * 2],
            &src_buf[block_size..block_size * 2],
        );
        let part_diff = diff_slice(
            &data[block_size * 2..(block_size * 2) + partition_entry_size],
            &src_buf[block_size * 2..(block_size * 2) + partition_entry_size],
        );
        eprintln!("MBR Diff: {}", mbr_diff);
        eprintln!("GPT Diff: {}", gpt_diff);
        eprintln!("Partition Diff: {}", part_diff);
        //
        assert_eq!(mbr_diff.diff.len(), 1, "MBR Diff has changes");
        assert_eq!(gpt_diff.diff.len(), 1, "GPT Diff has changes");
        assert_eq!(part_diff.diff.len(), 1, "Partition Diff has changes");
        match (&mbr_diff.diff[0], &gpt_diff.diff[0], &part_diff.diff[0]) {
            (DiffOp::Equal(_), DiffOp::Equal(_), DiffOp::Equal(_)) => (),
            (_, _, _) => panic!("Diffs are wrong"),
        }
        Ok(())
    }

    /// Test that struct sizes are what we expect
    #[test]
    fn size() {
        assert_eq_size!(GptPart, [u8; 128]);
        // Strictly speaking it should be 92, but should be fine
        // since we only depend on the first 92 bytes, and the rest is padding.
        assert_eq_size!(GptHeader, [u8; 96]);
    }
}
