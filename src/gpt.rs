//! Gpt Definitions
use crate::mbr::*;
use crate::partitions::*;
use crate::types::*;
use crc::{crc32, Hasher32};
use displaydoc::Display;
use generic_array::{typenum::U36, GenericArray};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::io::{prelude::*, SeekFrom};
use thiserror::Error;
use uuid::Uuid;

/// GPT Error Type.
#[allow(clippy::large_enum_variant)]
#[derive(Error, Debug, Display)]
pub enum NewGptError {
    /// Reading or writing the GPT failed
    Io(#[from] std::io::Error),

    /// Block sizes must be a power of two. (got: `{0}`)
    InvalidBlockSize(BlockSize),

    /// Invalid GPT header: `{0}`
    InvalidHeader(GptValidationErrorKind),

    /// The GPT is corrupt and not recoverable
    InvalidGpt,

    /// The size of the device does not match what the GPT Header expects. (expected: {0}, got {1})
    InvalidDiskSize(ByteSize, ByteSize),

    /// Unknown Error
    Unknown,
}

///
#[derive(Debug, Display)]
pub enum GptValidationErrorKind {
    /// GPT Signature invalid. (expected: `{EFI_PART}`, got `{0}`)
    InvalidSignature(u64),
}

type Result<T, E = NewGptError> = std::result::Result<T, E>;

const EFI_PART: u64 = 0x5452_4150_2049_4645;
const MIN_PARTITIONS_BYTES: u64 = 16384;

/// Check the validity of a GPT Header
///
/// # Arguments
///
/// - `header`, the GptHeader to validate. Despite being `&mut`,
///     this won't be visibly modified.
/// - `source`, the `Read`er for the device.
///     The position of this is expected to be directly after the GPT Header.
/// - `block_size`, devices block size.
///
/// # Errors
///
/// - If the header is invalid
/// - If calculating the CRC fails.
///
/// # Details
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
    block_size: BlockSize,
) -> Result<()> {
    if header.signature != EFI_PART {
        return Err(NewGptError::InvalidHeader(
            GptValidationErrorKind::InvalidSignature(header.signature),
        ));
    };
    if header.header_size < 92 || u64::from(header.header_size) >= block_size.0 {
        // return Err(GptError::INVALID_HEADER_SIZE.into());
    };
    // FIXME: This one shouldn't be a requirement.
    if header.header_size > 92 {
        // return Err(GptError::INVALID_HEADER_SIZE.into());
    };
    let old_crc = std::mem::replace(&mut header.header_crc32, 0);
    let crc = calculate_crc(header);
    header.header_crc32 = old_crc;
    if crc != old_crc {
        // return Err(GptError::INVALID_CHECKSUM.into());
    };
    //
    let current_lba = LogicalBlockAddress(source.seek(SeekFrom::Current(0))? / block_size.0);
    if header.this_lba != current_lba {
        // return Err(GptError::INVALID_LBA.into());
    };
    //
    source.seek(SeekFrom::Start(
        (header.partition_array_start * block_size).as_bytes(),
    ))?;
    let mut buf = [0u8; 128];
    //
    let mut digest = crc32::Digest::new(crc32::IEEE);
    for _ in 0..header.partitions {
        let times = header.partition_size / 128;
        for _ in 0..times {
            source.read_exact(&mut buf)?;
            digest.write(&buf);
        }
    }
    let crc = digest.sum32();
    if crc != header.partitions_crc32 {
        // return Err(GptError::INVALID_PART_CHECKSUM.into());
    }
    //
    Ok(())
}

/// Calculate the Header CRC for a [`GptHeader`].
///
/// [`GptHeader::header_crc32`] MUST be zero for this to be correct.
///
/// # Errors
///
/// - If bincode does.
fn calculate_crc(header: &GptHeader) -> u32 {
    // This is safe because `GptHeader` is `repr(C)`
    let source_bytes = unsafe {
        std::slice::from_raw_parts(
            (header as *const _) as *const u8,
            std::mem::size_of::<GptHeader>(),
        )
    };
    // NOTE: Only supported header size is really `92`..
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
// TODO: Add proper tests for this. Currently only `create_test_parts` fails.
fn uuid_hack(uuid: Uuid) -> Uuid {
    let (a, b, c, d) = uuid.to_fields_le();
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
    this_lba: LogicalBlockAddress,

    /// The logical block address the backup header is in
    alt_lba: LogicalBlockAddress,

    /// Where partitions can start
    first_usable_lba: LogicalBlockAddress,

    /// Where partitions must end
    last_usable_lba: LogicalBlockAddress,

    /// Disk GUID
    #[serde(with = "uuid::adapter::compact")]
    disk_guid: Uuid,

    /// Where our partition array starts on disk.
    partition_array_start: LogicalBlockAddress,

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
    /// - [`GptHeader::this_lba`]
    /// - [`GptHeader::alt_lba`]
    /// - [`GptHeader::first_usable_lba`]
    /// - [`GptHeader::last_usable_lba`]
    /// - [`GptHeader::partition_array_start`]
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

    /// Read the GPT Header from a [`Read`]er.
    ///
    /// # Errors
    ///
    /// - If IO does
    ///
    /// The [`Read`]ers current position is undefined after this call.
    fn from_reader<R: Read>(mut source: R) -> Result<Self> {
        Ok(
            bincode::deserialize_from(&mut source).map_err(|e| match *e {
                bincode::ErrorKind::Io(e) => NewGptError::Io(e),
                _ => NewGptError::Unknown,
            })?,
        )
    }

    /// Write the GPT Header to a [`Write`]r.
    ///
    /// # Errors
    ///
    /// - If IO does
    fn to_writer<W: Write>(&self, mut dest: W, block_size: u64) -> Result<()> {
        bincode::serialize_into(&mut dest, self).map_err(|e| match *e {
            bincode::ErrorKind::Io(e) => NewGptError::Io(e),
            _ => NewGptError::Unknown,
        })?;
        // Account for reserved space.
        let len = (block_size - 92) as usize;
        dest.write_all(&vec![0; len])?;
        Ok(())
    }
}

/// A GPT Partition
///
/// # Examples
///
/// List all partitions on a device
///
/// ```rust
/// use parts::{Gpt, GptPartBuilder, types::*};
/// use std::fs::File;
///
/// static PATH: &str = "tests/data/test_parts";
/// // A reasonable-ish default size.
/// const BLOCK_SIZE: BlockSize = BlockSize(512);
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut gpt = Gpt::from_reader(File::open(PATH)?, BLOCK_SIZE)?;
/// let part = GptPartBuilder::new(BLOCK_SIZE)
///     .name("Example")
///     .size((BLOCK_SIZE * 2).into())
///     .start(34.into())
///     .finish();
/// for part in gpt.partitions() {
///     match part.name() {
///         Some(name) => println!("Partition Name: {}", name),
///         None => println!("Partition has no name!"),
///     };
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Serialize, Deserialize)]
// This type is not safe to clone, but tests need it.
#[cfg_attr(test, derive(Clone, PartialEq))]
#[repr(C)]
pub struct GptPart {
    /// Defines the type of this partition
    #[serde(with = "uuid::adapter::compact")]
    partition_type_guid: Uuid,

    /// Unique identifer for this partition
    #[serde(with = "uuid::adapter::compact")]
    partition_guid: Uuid,

    /// Where it starts on disk
    starting_lba: LogicalBlockAddress,

    /// Where it ends on disk
    ending_lba: LogicalBlockAddress,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Null-terminated name, UCS-2/UTF-16LE string,
    name: GenericArray<u16, U36>,
}

impl fmt::Debug for GptPart {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("GptPart")
            .field("partition_type_guid", &self.part_type())
            .field("partition_guid", &self.partition_guid)
            .field("starting_lba", &self.starting_lba)
            .field("ending_lba", &self.ending_lba)
            .field("attributes", &self.attributes)
            .field("name", &self.name())
            .finish()
    }
}

impl GptPart {
    /// Name of the partition, if any.
    ///
    /// The conversion to [`String`] from the native UTF-16 may be lossy.
    pub fn name(&self) -> Option<String> {
        if self.name[0] != 0 {
            Some(String::from_utf16_lossy(
                self.name.as_slice().split(|n| *n == 0).next().unwrap(),
            ))
        } else {
            None
        }
    }

    /// Type of the Partition
    ///
    /// See [`PartitionType`] for details
    pub fn part_type(&self) -> PartitionType {
        PartitionType::from_uuid(uuid_hack(self.partition_type_guid))
    }

    /// The starting logical block address for the partition.
    pub fn start(&self) -> LogicalBlockAddress {
        self.starting_lba
    }

    /// The ending logical block address for the partition.
    ///
    /// Note that this is inclusive.
    ///
    /// # Examples
    ///
    /// Creating aligned partitions
    ///
    /// ```rust
    /// # use parts::{types::*, Gpt, GptPartBuilder};
    /// let block_size = BlockSize(512);
    /// let image_size = ByteSize::from_mib(30);
    /// //
    /// let mut gpt = Gpt::new(block_size, image_size);
    /// let mib_aligned = ByteSize::from_mib(1) / block_size;
    ///
    /// let first_part = GptPartBuilder::new(block_size)
    ///     .name("First")
    ///     .size(ByteSize::from_mib(10))
    ///     .start(mib_aligned)
    ///     .finish();
    ///
    /// let second_part = GptPartBuilder::new(block_size)
    ///     .name("Second")
    ///     .size(ByteSize::from_mib(10))
    ///     .start(first_part.end() + 1) // This will also be 1MiB aligned!
    ///     .finish();
    ///
    /// gpt.add_partition(first_part);
    /// gpt.add_partition(second_part);
    /// ```
    pub fn end(&self) -> LogicalBlockAddress {
        self.ending_lba
    }
}

impl GptPart {
    /// Reads a GPT Partition from a [`Read`]er.
    ///
    /// This will advance the [`Read`]er by the size of a single partition entry.
    ///
    /// `size_of` is [`GptHeader::partition_size`]
    fn from_reader<R: Read + Seek>(mut source: R, size_of: u32) -> Result<Self> {
        let obj = bincode::deserialize_from(&mut source).map_err(|e| match *e {
            bincode::ErrorKind::Io(e) => NewGptError::Io(e),
            _ => NewGptError::Unknown,
        })?;
        // Seek past the remaining block.
        source.seek(SeekFrom::Current(i64::from(size_of) - 128))?;
        Ok(obj)
    }

    /// Write a GPT Partition to a [`Write`]r
    fn to_writer<W: Write>(&self, mut dest: W, size_of: u32) -> Result<()> {
        bincode::serialize_into(&mut dest, self).map_err(|e| match *e {
            bincode::ErrorKind::Io(e) => NewGptError::Io(e),
            _ => NewGptError::Unknown,
        })?;
        // Account for reserved space.
        let len = (size_of - 128) as usize;
        dest.write_all(&vec![0; len])?;
        Ok(())
    }

    /// Used by tests.
    ///
    /// Don't derive [`Default`] because this type is public,
    /// and that wouldn't be valid.
    // FIXME: Derive Default anyway, we have cfg_attr?!
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
///
/// # Notes
///
/// If you do not specify [`GptPartBuilder::size`],
/// it will be rounded to the `block_size`, which is the minimum possible size.
///
/// # Examples
///
/// See [parts](./index.html)
///
/// See method documentation
#[derive(Debug)]
pub struct GptPartBuilder {
    partition_type_guid: Uuid,

    partition_guid: Uuid,

    start_lba: LogicalBlockAddress,

    size: ByteSize,

    name: String,

    block_size: BlockSize,
}

impl GptPartBuilder {
    /// Create a new Gpt Partition.
    ///
    /// # Examples
    ///
    /// See [`GptPartBuilder`]
    pub fn new(block_size: BlockSize) -> Self {
        Self {
            partition_type_guid: Uuid::nil(),
            partition_guid: Uuid::new_v4(),
            start_lba: Default::default(),
            size: Default::default(),
            name: Default::default(),
            block_size,
        }
    }

    /// Create a [`GptPartBuilder`] based on an existing [`GptPart`].
    ///
    /// This allows you to modify an existing GptPart,
    /// perhaps from [`Gpt::remove_partition`]
    ///
    /// # Notes
    ///
    /// The conversion of the partition name from UTF-16 to UTF-8 may be lossy.
    pub fn from_part(part: GptPart, block_size: BlockSize) -> Self {
        GptPartBuilder {
            partition_type_guid: part.partition_type_guid,
            partition_guid: part.partition_guid,
            start_lba: part.starting_lba,
            size: ((part.ending_lba - part.starting_lba) * block_size) + block_size.into(),
            name: String::from_utf16_lossy(part.name.as_slice()),
            block_size,
        }
    }

    /// Set the name of the partition.
    ///
    /// `name` must be no more than 35 characters.
    pub fn name(mut self, name: &str) -> Self {
        assert!(name.len() < 36, "Name too long");
        self.name = name.into();
        self
    }

    /// Size of the partition, according to [`ByteSize`]
    ///
    /// # Notes
    ///
    /// Partitions can only be represented in logical block addresses,
    /// so this size should be divisible by the device block size.
    ///
    /// If it's not, the size will be rounded up.
    pub fn size(mut self, mut size: ByteSize) -> Self {
        if (size % self.block_size.0) != ByteSize::from_bytes(0) {
            size += ByteSize::from(self.block_size) - (size % self.block_size.0)
        }
        self.size = size;
        self
    }

    /// Which [`LogicalBlockAddress`] the partition should at start on disk.
    ///
    /// The ending address will be automatically calculated from
    /// the size of the partition and the starting point specified here.
    ///
    /// # Examples
    ///
    /// Align at a 1MiB boundary.
    /// Note that this will only work if [`GptPartBuilder::size`] is
    /// a multiple of 1MiB.
    ///
    /// ```rust
    /// # use parts::*;
    /// # use parts::types::*;
    /// let block_size = BlockSize(512);
    /// let part = GptPartBuilder::new(block_size)
    ///     .size(ByteSize::from_mib(1))
    ///     .start(ByteSize::from_mib(1) / block_size)
    ///     .finish();
    /// ```
    pub fn start(mut self, lba: LogicalBlockAddress) -> Self {
        self.start_lba = lba;
        self
    }

    /// Set the partition GUID.
    ///
    /// # Safety
    ///
    /// This is unsafe because GPT Partition GUID's are supposed to be unique.
    ///
    /// Having two partitions with the same GUID is a violation of the spec.
    pub unsafe fn part_guid(mut self, part_guid: Uuid) -> Self {
        self.partition_guid = uuid_hack(part_guid);
        self
    }

    /// Partition type GUID.
    pub fn part_type(mut self, part_type: PartitionType) -> Self {
        // FIXME: uuid_hack strikes again
        self.partition_type_guid = uuid_hack(part_type.to_uuid());
        self
    }

    /// Finalize the Gpt Partition.
    pub fn finish(mut self) -> GptPart {
        if self.size.as_bytes() == 0 {
            self.size = self.block_size.into();
        }
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
///
///
/// All modifications are done in-memory and
/// the *only* method that will modify a real device/file is
/// [`Gpt::to_writer`].
///
/// # Usage
///
/// See [`Gpt::new`] and [`Gpt::from_reader`]
///
/// # Panics
///
/// It is possible to create an invalid [`Gpt`] instance,
/// for the purposes of repairing it.
///
/// Using such an instance without repairing it may cause certain methods to panic.
/// The only method safe to use is [`Gpt::repair`].
#[derive(Debug)]
// Comparing this doesn't make sense except in tests.
#[cfg_attr(test, derive(PartialEq))]
pub struct Gpt {
    mbr: ProtectiveMbr,

    /// Can be None if corrupt
    header: Option<GptHeader>,

    /// Can be None if corrupt
    backup: Option<GptHeader>,

    partitions: Vec<GptPart>,

    /// The devices block size. ex, 512, 4096
    block_size: BlockSize,

    /// Size of entire disk, in bytes.
    disk_size: ByteSize,
}

/// Public
impl Gpt {
    /// Create a new GPT label,
    /// assuming a size of `disk_size` and a block size of `block_size`
    ///
    /// This creates a valid, but empty, Gpt Label.
    ///
    /// # Examples
    ///
    /// Create a new Gpt Table and add a partition.
    ///
    /// ```rust
    /// # use parts::{Gpt, GptPartBuilder};
    /// # use parts::types::*;
    /// # let block_size = BlockSize(512);
    /// # let disk_size = (block_size * 100).into();
    /// let mut gpt = Gpt::new(block_size, disk_size);
    /// let part = GptPartBuilder::new(block_size)
    ///     .name("Example")
    ///     .size((block_size * 2).into())
    ///     .start(LogicalBlockAddress(34))
    ///     .finish();
    /// gpt.add_partition(part);
    /// ```
    ///
    /// # Panics
    ///
    /// - If `disk_size` isn't large enough.
    ///
    /// Specifically, `disk_size` must be large enough to fit
    /// the GPT Header, the minimum required Gpt Partition array,
    /// and their backups.
    ///
    /// For a `block_size` of 512, this is 512 * 67.
    /// Two blocks at the start, the MBR and GPT header,
    /// 32 blocks for the partition array, one for the backup GPT header,
    /// and 32 blocks for the backup partition array.
    ///
    /// Note that such a small size has no room for any partitions.
    pub fn new(block_size: BlockSize, disk_size: ByteSize) -> Self {
        // logical block addresses start at zero.
        let last_lba = (disk_size / block_size) - 1;
        let min_partition_blocks = ByteSize::from_bytes(MIN_PARTITIONS_BYTES) / block_size;
        //
        assert!(
            (last_lba + 1) >= ((min_partition_blocks * 2) + 3),
            "disk_size is too small to hold the GPT"
        );
        //
        let mbr = ProtectiveMbr::new(last_lba);
        //
        let mut header = GptHeader::new();
        header.this_lba = 1.into();
        header.alt_lba = last_lba;
        // Plus two blocks, one for the MBR and one for the GPT Header.
        header.first_usable_lba = min_partition_blocks + 2;
        // Minus 1 block for the GPT Header
        header.last_usable_lba = last_lba - min_partition_blocks - 1;
        header.partition_array_start = 2.into();
        header.header_crc32 = calculate_crc(&header);
        //
        let mut backup: GptHeader = header.clone();
        backup.this_lba = last_lba;
        backup.alt_lba = 1.into();
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

    /// Read from an existing GPT Disk or image.
    ///
    /// # Arguments
    ///
    /// - `block_size` is the devices logical block size. ex: 512, 4096
    ///
    /// # Examples
    ///
    /// Read from an in-memory representation.
    ///
    /// ```rust
    /// # use std::io::Cursor;
    /// # use parts::Gpt;
    /// # use parts::types::*;
    /// # const TEN_MIB_BYTES: usize = 10485760;
    /// # const BLOCK_SIZE: BlockSize = BlockSize(512);
    /// let mut data = Cursor::new(vec![0; TEN_MIB_BYTES]);
    /// let gpt = Gpt::from_reader(&mut data, BLOCK_SIZE);
    /// ```
    ///
    /// # Errors
    ///
    /// - If IO fails.
    /// - If the Protective MBR is invalid.
    /// - If the primary and/or backup GPT is invalid.
    ///
    /// ## Invalid GPT Headers
    ///
    /// In this case the [`Err`] variant will contain a [`Gpt`] Instance,
    /// which should be repaired after asking permission from the user.
    ///
    /// If both the primary and backup GPT is corrupt, repairing will not be possible.
    pub fn from_reader<RS>(mut source: RS, block_size: BlockSize) -> Result<Self>
    where
        RS: Read + Seek,
    {
        if !(block_size.0).is_power_of_two() {
            return Err(NewGptError::InvalidBlockSize(block_size));
        }
        //
        let _disk_size = {
            let cur = source.seek(SeekFrom::Current(0))?;
            let end = ByteSize::from_bytes(source.seek(SeekFrom::End(0))?);
            source.seek(SeekFrom::Start(cur))?;
            end
        };
        //
        let _mbr = match ProtectiveMbr::from_reader(&mut source, block_size) {
            Err(MbrError::Io(e)) => return Err(NewGptError::Io(e)),
            mbr @ Err(MbrError::QuirkBrokenPartedCHS(_)) => mbr,
            _ => return Err(NewGptError::Unknown),
        };
        //
        let header = GptHeader::from_reader(&mut source).and_then(|mut x| {
            match check_validity(&mut x, &mut source, block_size) {
                Ok(_) => Ok(x),
                Err(e) => Err(e),
            }
        });

        let mut partitions = Vec::new();

        if let Ok(header) = &header {
            source.seek(SeekFrom::Start(
                (header.partition_array_start * block_size).as_bytes(),
            ))?;
            partitions.reserve_exact(header.partitions as usize);
            for _ in 0..header.partitions {
                let part = GptPart::from_reader(&mut source, header.partition_size)?;
                // Ignore unused partitions, so `partitions` isn't cluttered.
                // Shouldn't cause any problems since unused partitions are all zeros.
                if part.partition_type_guid != Uuid::nil() {
                    partitions.push(part);
                }
            }
            // Prepare for the backup GPT header to be read.
            source.seek(SeekFrom::Start((header.alt_lba * block_size).as_bytes()))?;
        } else {
            source.seek(SeekFrom::End(-(block_size.0 as i64)))?;
        }
        //
        let backup = GptHeader::from_reader(&mut source).and_then(|mut x| {
            match check_validity(&mut x, &mut source, block_size) {
                Ok(_) => Ok(x),
                Err(e) => Err(e),
            }
        });

        if let Ok(backup) = &backup {
            source.seek(SeekFrom::Start(
                (backup.partition_array_start * block_size).as_bytes(),
            ))?;
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

        //
        unimplemented!()

        // match (header, backup) {
        //     (Err(_), Err(_)) => Err(NewGptError::InvalidGpt),
        //     (Ok(header), Ok(backup)) => Ok(Self {
        //         mbr,
        //         header: Some(header),
        //         backup: Some(backup),
        //         partitions,
        //         block_size,
        //         disk_size,
        //     }),
        //     (Ok(h), Err(e)) => Err(GptError::CorruptGpt(
        //         Self {
        //             mbr,
        //             header: Some(h),
        //             backup: None,
        //             partitions,
        //             block_size,
        //             disk_size,
        //         },
        //         e.into(),
        //     )),
        //     (Err(e), Ok(b)) => Err(GptError::CorruptGpt(
        //         Self {
        //             mbr,
        //             header: None,
        //             backup: Some(b),
        //             partitions,
        //             block_size,
        //             disk_size,
        //         },
        //         e.into(),
        //     )),
        // }
    }

    /// Set the disk GUID.
    ///
    /// # Safety
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

    /// Write the GPT structure to a [`Write`]r.
    ///
    /// # Errors
    ///
    /// - If IO does.
    /// - If `dest` is a different size than expected.
    /// GPT requires that the last logical block address be
    /// the backup GPT Header. If `dest` has grown larger, both headers
    /// will need updating.
    ///
    /// # Panics
    ///
    /// - If this [`Gpt`] instance is corrupt.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use parts::Gpt;
    /// # use parts::types::*;
    /// use std::io::Cursor;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let block_size = BlockSize(512);
    /// # let disk_size = (block_size * 100).into();
    /// let gpt = Gpt::new(block_size, disk_size);
    /// let mut buffer = Cursor::new(vec![0; disk_size.as_bytes() as usize]);
    /// gpt.to_writer(&mut buffer)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_writer<W: Write + Seek>(&self, mut dest: W) -> Result<()> {
        let header = self.header.as_ref().unwrap();
        let backup = self.backup.as_ref().unwrap();
        //
        let disk_size = {
            let cur = dest.seek(SeekFrom::Current(0))?;
            let end = dest.seek(SeekFrom::End(0))?;
            dest.seek(SeekFrom::Start(cur))?;
            ByteSize::from_bytes(end)
        };
        if disk_size != self.disk_size {
            // return Err(NewGptError::InvalidSize);
            return Err(NewGptError::InvalidDiskSize(self.disk_size, disk_size));
        }
        //
        self.mbr
            .to_writer(&mut dest, self.block_size)
            .map_err(|e| match e {
                MbrError::Io(e) => NewGptError::Io(e),
                _ => NewGptError::Unknown,
            })?;

        header.to_writer(&mut dest, self.block_size.0)?;

        dest.seek(SeekFrom::Start(
            (header.partition_array_start * self.block_size).as_bytes(),
        ))?;
        for part in &self.partitions {
            part.to_writer(&mut dest, header.partition_size)?;
        }

        dest.seek(SeekFrom::Start(
            (header.alt_lba * self.block_size).as_bytes(),
        ))?;
        backup.to_writer(&mut dest, self.block_size.0)?;

        dest.seek(SeekFrom::Start(
            (backup.partition_array_start * self.block_size).as_bytes(),
        ))?;
        for part in &self.partitions {
            part.to_writer(&mut dest, backup.partition_size)?;
        }

        //
        Ok(())
    }

    /// Repair an invalid GPT instance.
    ///
    /// An invalid GPT instance is one with a corrupt or missing
    /// backup or primary label.
    ///
    /// Repairing such an instance involves duplicating the existing label
    /// and replacing the corrupt area.
    ///
    /// Only call this method with permission from the user.
    ///
    /// # Examples
    ///
    /// Pseudo-code showing how to repair a corrupt [`Gpt`]
    ///
    /// ```rust,compile_fail
    /// let corrupt_gpt = Gpt::from_reader(Cursor::new(&mut corrupted_buf), BLOCK_SIZE);
    /// match corrupt_gpt {
    ///     Err(GptError::CorruptGpt(mut gpt, _)) => {
    ///         assert_eq!(gpt.header, None);
    ///         assert_eq!(gpt.backup, Some(_));
    ///         gpt.repair();
    ///         assert_eq!(gpt.header, uncorrupted_gpt.header);
    ///     }
    /// }
    /// ```
    pub fn repair(&mut self) {
        if self.header.is_none() || self.backup.is_none() {
            let last_lba = (self.disk_size / self.block_size) - 1;
            if let Some(header) = &self.header {
                let mut backup = header.clone();
                backup.this_lba = last_lba;
                backup.alt_lba = 1.into();
                backup.partition_array_start = header.last_usable_lba + 1;
                backup.header_crc32 = 0;
                backup.header_crc32 = calculate_crc(&backup);
                self.backup = Some(backup);
            } else if let Some(backup) = &self.backup {
                let mut header = backup.clone();
                header.this_lba = 1.into();
                header.alt_lba = last_lba;
                header.partition_array_start = 2.into();
                header.header_crc32 = 0;
                header.header_crc32 = calculate_crc(&header);
                self.header = Some(header);
            }
        }
    }

    /// Iterator of the available partitions.
    pub fn partitions(&self) -> &[GptPart] {
        &self.partitions
    }

    /// Adds a new partition
    ///
    /// # Examples
    ///
    /// See [`Gpt::new`]
    ///
    /// # Panics
    ///
    /// - If the [`GptPart`] doesn't fit
    /// within the first/last usable logical block addresses.
    /// - If `part` overlaps with any existing partition.
    pub fn add_partition(&mut self, part: GptPart) {
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        assert!(
            part.starting_lba >= header.first_usable_lba,
            format!(
                "Invalid Partition Span: {:?}",
                (part.starting_lba, part.ending_lba)
            )
        );
        assert!(
            part.ending_lba <= header.last_usable_lba,
            format!(
                "Invalid Partition Span: {:?}",
                (part.starting_lba, part.ending_lba)
            )
        );
        for existing in &self.partitions {
            if part.starting_lba >= existing.starting_lba
                && part.starting_lba <= existing.ending_lba
            {
                panic!(
                    "Attempted to add overlapping partitions. `{:#?}` overlaps with `{:#?}`",
                    part, existing
                );
            }
        }
        // FIXME: Support more partitions.
        // This would require moving the first usable lba forward, and the last usable one back.
        assert!(header.partitions <= 128, "Too many partitions");
        //
        self.partitions.push(part);
        // `GptHeader::partitions` can be larger than the
        // actual number of partitions, at least in practice.
        if self.partitions.len() > header.partitions as usize {
            header.partitions += 1;
            backup.partitions += 1;
        }
        //
        self.recalculate_part_crc();
    }

    /// Remove an existing partition at the index `index`.
    ///
    /// Returns the removed partition.
    /// This allows you to modify it using [`GptPartBuilder::from_part`] and then re-add it.
    ///
    /// Note that indexing starts at zero.
    ///
    /// # Panics
    ///
    /// - If `index` is out of bounds.
    pub fn remove_partition(&mut self, index: usize) -> GptPart {
        self.partitions.swap_remove(index)
    }

    /// Get the first logical block address you can use for partitions.
    /// This is useful with [`GptPartBuilder`]
    pub fn first_usable_address(&self) -> LogicalBlockAddress {
        self.header.as_ref().unwrap().first_usable_lba
    }

    /// Get the last logical block address you can use for partitions.
    /// This is useful with [`GptPartBuilder`]
    pub fn last_usable_address(&self) -> LogicalBlockAddress {
        self.header.as_ref().unwrap().last_usable_lba
    }

    /// If the underlying device has somehow grown larger,
    /// you won't be able to use [`Gpt::to_writer`].
    ///
    /// This will update the GPT and allow it to be written.
    pub fn update_disk_size(&mut self, new_size: ByteSize) {
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        self.disk_size = new_size;
        let min_partition_blocks = ByteSize::from_bytes(MIN_PARTITIONS_BYTES) / self.block_size;
        let last_lba = (self.disk_size / self.block_size) - 1;
        //
        header.last_usable_lba = last_lba - min_partition_blocks - 1;
        backup.this_lba = last_lba;
        self.recalculate_crc();
    }

    /// Returns the remaining size on disk for a partition starting at
    /// the `start` [`LogicalBlockAddress`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use parts::*;
    /// # use parts::types::*;
    /// # let block_size = BlockSize(512);
    /// let image_size = ByteSize::from_mib(100);
    ///
    /// let gpt = Gpt::new(block_size, image_size);
    /// let first_part = GptPartBuilder::new(block_size)
    ///     .name("First")
    ///     .size(ByteSize::from_mib(1))
    ///     .start(ByteSize::from_mib(1) / block_size)
    ///     .finish();
    /// let remaining_part = GptPartBuilder::new(block_size)
    ///     .name("Remaining")
    ///     .size(gpt.remaining(first_part.end() + 1))
    ///     .start(first_part.end() + 1)
    ///     .finish();
    /// let part_size = ((remaining_part.end() - remaining_part.start()) + 1) * block_size;
    ///
    /// // 1MiB for padding, then 1MiB for `first_part`,
    /// // and then 17 * 2(34KiB) for the GPT headers.
    /// let expected_remaining = ByteSize::from_mib(98) - (ByteSize::from_kib(17) * 2);
    ///
    /// assert_eq!(part_size, expected_remaining)
    /// ```
    pub fn remaining(&self, start: LogicalBlockAddress) -> ByteSize {
        ((self.last_usable_address() - self.first_usable_address()) - start) * self.block_size
    }
}

/// Private
impl Gpt {
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
    /// This also calls [`Gpt::recalculate_crc`], since updating the partition crc
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
    use super::*;
    use static_assertions::*;
    use std::{error::Error, io::Cursor};
    use uuid::Uuid;

    static TEST_PARTS: &str = "tests/data/test_parts";
    static TEST_PARTS_CF: &str = "tests/data/test_parts_cf";
    const BLOCK_SIZE: BlockSize = BlockSize(512);
    const LARGE_BLOCK_SIZE: BlockSize = BlockSize(4096);
    // 10 * 1024^2
    const TEN_MIB_BYTES: usize = 10_485_760;

    const CF_DISK_GUID: &str = "A17875FB-1D86-EE4D-8DFE-E3E8ABBCD364";
    const CF_PART_GUID: &str = "97954376-2BB6-534B-A015-DF434A94ABA2";
    const LINUX_PART_GUID: PartitionType = PartitionType::LinuxFilesystemData;

    type Result = std::result::Result<(), Box<dyn Error>>;

    // We rely on GptPart being exactly 128 bytes for crc calculation,
    // directly from a `Vec<GptPart>`.
    assert_eq_size!(GptPart, [u8; 128]);

    // Strictly speaking it should be 92, but should be fine
    // since we only depend on the first 92 bytes, and the rest is padding.
    assert_eq_size!(GptHeader, [u8; 96]);

    /// Tests that we can read an external GPT layout,
    /// serialize it, and deserialize it again, with it staying the same.
    #[test]
    fn gpt_roundtrip() -> Result {
        let file = std::fs::File::open(TEST_PARTS)?;
        //
        let src_gpt = Gpt::from_reader(file, BLOCK_SIZE)?;
        //
        let mut buf = Cursor::new(vec![0; TEN_MIB_BYTES]);
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
        let mut buf = Cursor::new(vec![0; TEN_MIB_BYTES]);
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
        let mut gpt = Gpt::new(
            BLOCK_SIZE,
            ByteSize::from_bytes(data.get_ref().len() as u64),
        );
        let mut part = GptPartBuilder::new(BLOCK_SIZE)
            .size(ByteSize::from_mib(8))
            .start(ByteSize::from_mib(1) / BLOCK_SIZE)
            .part_type(LINUX_PART_GUID);
        dbg!(&part);
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
        gpt.header.as_mut().unwrap().first_usable_lba = LogicalBlockAddress(2048);
        gpt.backup.as_mut().unwrap().first_usable_lba = LogicalBlockAddress(2048);
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

        let block_size = BLOCK_SIZE.0 as usize;
        let partition_entry_size = 128;
        // Not an ideal comparison, useless for debugging, but..
        let mbr_new = &data[..block_size];
        let mbr_old = &src_buf[..block_size];
        //
        let gpt_new = &data[block_size..block_size * 2];
        let gpt_old = &src_buf[block_size..block_size * 2];
        //
        let part_new = &data[block_size * 2..(block_size * 2) + partition_entry_size];
        let part_old = &src_buf[block_size * 2..(block_size * 2) + partition_entry_size];
        //
        assert_eq!(mbr_new, mbr_old, "MBR is incorrect");
        assert_eq!(gpt_new, gpt_old, "GPT is incorrect");
        assert_eq!(part_new, part_old, "Partition is incorrect");
        Ok(())
    }

    /// Test that we don't crash on header sizes
    /// larger than the block size, or larger than [`GptHeader`]
    #[test]
    fn large_header_size() -> Result {
        let disk_size = BLOCK_SIZE * 100;
        let mut gpt = Gpt::new(BLOCK_SIZE, disk_size.into());
        let header = gpt.header.as_mut().unwrap();
        let backup = gpt.backup.as_mut().unwrap();
        header.header_size = (BLOCK_SIZE * 2).0 as u32;
        backup.header_size = (BLOCK_SIZE * 2).0 as u32;
        // Don't recalculate the crc32 here, because the problem we're testing
        // comes *from* calculating the crc32.
        //
        let mut v = Cursor::new(vec![0; disk_size.0 as usize]);
        gpt.to_writer(&mut v)?;
        let gpt = Gpt::from_reader(&mut v, BLOCK_SIZE).unwrap_err();
        dbg!(&gpt);
        Ok(())
    }

    /// Test large block sizes
    #[test]
    fn large_block_size() -> Result {
        let disk_size = LARGE_BLOCK_SIZE * 100;
        let gpt = Gpt::new(LARGE_BLOCK_SIZE, disk_size.into());
        dbg!(&gpt);
        let header = gpt.header.as_ref().unwrap();
        let backup = gpt.backup.as_ref().unwrap();
        assert!(header.first_usable_lba >= LogicalBlockAddress(6));
        assert!(backup.first_usable_lba >= LogicalBlockAddress(6));
        Ok(())
    }

    /// Ensure that [`Gpt::new`] panics if the disk is too small.
    #[test]
    #[should_panic(expected = "disk_size is too small")]
    fn small_disk() {
        let disk_size = BLOCK_SIZE * 30;
        let _gpt = Gpt::new(BLOCK_SIZE, disk_size.into());
    }

    /// Ensure that [`Gpt::new`] doesn't panics if the disk is
    /// exactly the minimum size.
    ///
    /// Prevent an off-by-one error in minimum size checking.
    #[test]
    fn minimum_disk_regress() {
        let disk_size = BLOCK_SIZE * 67;
        let _gpt = Gpt::new(BLOCK_SIZE, disk_size.into());
    }

    /// Ensure that the GPT can properly be repaired if only one header is corrupt.
    #[test]
    fn corrupt_gpt_test() {
        let mut file = std::fs::File::open(TEST_PARTS_CF).unwrap();
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf).unwrap();
        //
        let _src_gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE).unwrap();
        // Invalidate the primary GPT
        src_buf[512] = 0;
        //
        let _gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE);
        // match gpt {
        //     Err(GptError::CorruptGpt(mut gpt, _)) => {
        //         assert_eq!(gpt.header, None);
        //         gpt.repair();
        //         dbg!(&gpt.header);
        //         dbg!(&src_gpt.header);
        //         assert_eq!(gpt.header, src_gpt.header);
        //     }
        //     g => {
        //         dbg!(&g);
        //         eprintln!("{}", g.unwrap_err());
        //         panic!("`corrupt_gpt_test` unexpected error");
        //     }
        // }
    }

    /// Ensure that [`Gpt::from_reader`] properly fails if there is no
    /// primary or backup Gpt.
    #[test]
    #[should_panic]
    fn missing_gpt_test() {
        let data = Cursor::new(vec![0; TEN_MIB_BYTES]);
        let _gpt = Gpt::from_reader(data, BlockSize(512)).unwrap();
    }

    #[test]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    fn invalid_partitions() {
        let mut gpt = Gpt::new(BLOCK_SIZE, ByteSize::from_bytes(TEN_MIB_BYTES as u64));
        let part = GptPartBuilder::new(BLOCK_SIZE)
            .size(ByteSize::from_mib(8))
            .start(ByteSize::from_mib(1) / BLOCK_SIZE)
            .part_type(LINUX_PART_GUID)
            .finish();
        let dup_part = part.clone();
        gpt.add_partition(part);
        gpt.add_partition(dup_part);
    }

    /// Ensure that [`GptPartBuilder::finish`] doesn't create an invalid
    /// partition if [`GptPartBuilder::size`] isn't called.
    ///
    /// Previously it would generate a partition ending before it started
    ///
    /// The minimum size is now `block_size`
    #[test]
    fn gpt_part_builder_minimum_size() {
        let part = GptPartBuilder::new(BLOCK_SIZE).finish();
        assert_eq!(
            part.start(),
            part.end(),
            "GptPartBuilder invalid minimum size"
        );
    }
}
