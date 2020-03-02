//! Raw Gpt stuff
use crate::types::*;
use core::{convert::TryInto, mem, slice};
use crc::{crc32, Hasher32};
use displaydoc::Display;
#[cfg(any(feature = "std", test))]
use thiserror::Error;
use uuid::Uuid;

/// GPT stores UUID's in big endian, but with the time* fields as little endian.
///
/// See Appendix A for more details.
fn uuid_hack(uuid: [u8; 16]) -> Uuid {
    // Works because from_bytes treats the fields as big endian
    // as_fields types them for us, still big-endian
    // and swap_bytes swaps the bytes, making them little endian.
    // to_le_bytes can't be used because it's a no-op on little endian computers.
    // TODO: Replace with from_bytes_le if uuid ever adds that back. :(
    let uuid = Uuid::from_bytes(uuid);
    let (d1, d2, d3, d4) = uuid.as_fields();
    Uuid::from_fields(d1.swap_bytes(), d2.swap_bytes(), d3.swap_bytes(), d4).unwrap()
}

/// Calculate the Header CRC for a [`RawHeader`].
fn calculate_crc(mut header: RawHeader) -> u32 {
    header.header_crc32 = 0;
    // # Safety
    // - `RawHeader` is repr(C,packed)
    // - Pointer will always be valid
    // - size_of used
    let source_bytes = unsafe {
        slice::from_raw_parts(
            (&header as *const _) as *const u8,
            mem::size_of::<RawHeader>(),
        )
    };
    crc32::checksum_ieee(&source_bytes[..header.header_size as usize])
}

#[derive(Debug, Display)]
#[cfg_attr(any(feature = "std", test), derive(Error))]
pub enum Error {
    /// Not enough data was provided
    NotEnough,

    /// Encountered an unsupported GPT format
    Unsupported,

    /// The GPT Header was invalid: {0}
    Invalid(&'static str),
}

pub type Result<T> = core::result::Result<T, Error>;

/// "EFI PART" constant as a u64
const EFI_PART: u64 = 0x5452_4150_2049_4645;

/// Current/supported GPT Header revision
const REVISION: u32 = 0x0001_0000;

/// Current/supported GPT Header size.
///
/// Only used when writing, can in theory read and validate larger headers.
const HEADER_SIZE: u32 = 92;

/// Current/supported GPT Partition Entry size.
///
/// Only used when writing, can in theory read and validate larger entries.
const PARTITION_ENTRY_SIZE: u32 = 128;

/// A minimum of 16,384 bytes are reserved for the partition array.
///
/// With current GPT Partition entry sizes this means a minimum of 128
/// partitions
const MIN_PARTITIONS_BYTES: u64 = 16384;

/// Supported max partitions.
const MAX_PARTITIONS: usize = (MIN_PARTITIONS_BYTES / PARTITION_ENTRY_SIZE as u64) as usize;

/// The GPT Header Structure
#[derive(Debug, Copy, Clone)]
#[repr(C, packed)]
struct RawHeader {
    /// Hard-coded to [`EFI_PART`]
    signature: u64,

    /// Hard-coded to [`REVISION`]
    revision: u32,

    /// Soft-coded to [`HEADER_SIZE`]
    ///
    /// Must be header_size >= 92 and header_size <= logical block size.
    header_size: u32,

    /// CRC32(bytes[0..header_size])
    ///
    /// Set to zero when computing CRC
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

    /// Disk GUID. See [`uuid_hack`] for details.
    disk_guid: [u8; 16],

    /// Where our partition array starts on disk.
    partition_array_start: LogicalBlockAddress,

    /// Number of partitions
    partitions: u32,

    /// Size of each partition entry structure.
    /// Must be 128 * 2^n, where n >= 0
    partition_size: u32,

    /// CRC32 of the partition array
    partitions_crc32: u32,
}

impl Default for RawHeader {
    fn default() -> Self {
        RawHeader {
            signature: EFI_PART,
            revision: REVISION,
            header_size: HEADER_SIZE,
            partition_size: PARTITION_ENTRY_SIZE,
            // Default values
            header_crc32: Default::default(),
            _reserved: Default::default(),
            this_lba: Default::default(),
            alt_lba: Default::default(),
            first_usable_lba: Default::default(),
            last_usable_lba: Default::default(),
            disk_guid: Default::default(),
            partition_array_start: Default::default(),
            partitions: Default::default(),
            partitions_crc32: Default::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Header {
    /// The logical block address this header is in
    this_lba: LogicalBlockAddress,

    /// The logical block address the backup header is in
    alt_lba: LogicalBlockAddress,

    /// First valid LBA for partitions
    first_usable_lba: LogicalBlockAddress,

    /// Last valid LBA for partitions
    last_usable_lba: LogicalBlockAddress,

    /// Disk GUID
    disk_guid: Uuid,

    /// Number of partitions
    partitions: u32,

    /// Where the partition array starts on disk.
    partition_array_start: LogicalBlockAddress,

    /// CRC32 of the partition array
    partitions_crc32: u32,

    /// Size of each partition entry structure.
    /// Must be 128 * 2^n, where n >= 0
    partition_size: u32,
}

impl Header {
    /// Read the GPT Header from a byte slice
    ///
    /// # Errors
    ///
    /// - If `source` does not have enough data
    /// - The GPT is invalid.
    pub fn from_bytes(source: &mut &[u8], block_size: BlockSize) -> Result<Self> {
        let b_size = block_size.0.try_into().unwrap();
        if source.len() < b_size {
            return Err(Error::NotEnough);
        }
        // # Safety
        // - `source` is always a valid pointer
        // - Errors if `source` doesn't have enough data
        // - `RawHeader` is repr(C, packed)
        #[allow(clippy::cast_ptr_alignment)]
        let raw = unsafe {
            (source
                .get(..mem::size_of::<RawHeader>())
                .ok_or(Error::NotEnough)?
                .as_ptr() as *const RawHeader)
                .read_unaligned()
        };
        if raw.signature != EFI_PART {
            return Err(Error::Invalid("Invalid Signature"));
        }
        if raw.header_crc32 != calculate_crc(raw) {
            return Err(Error::Invalid("CRC mismatch"));
        }
        let header = Header {
            this_lba: raw.this_lba,
            alt_lba: raw.alt_lba,
            first_usable_lba: raw.first_usable_lba,
            last_usable_lba: raw.last_usable_lba,
            disk_guid: uuid_hack(raw.disk_guid),
            partitions: raw.partitions,
            partition_array_start: raw.partition_array_start,
            partitions_crc32: raw.partitions_crc32,
            partition_size: raw.partition_size,
        };
        *source = &source[b_size..];
        Ok(header)
    }

    /// Write the GPT header to `dest`
    pub fn to_bytes(&self, dest: &mut [u8]) -> Result<()> {
        let mut raw = RawHeader::default();
        raw.this_lba = self.this_lba;
        raw.alt_lba = self.alt_lba;
        raw.first_usable_lba = self.first_usable_lba;
        raw.last_usable_lba = self.last_usable_lba;
        raw.disk_guid = *uuid_hack(*self.disk_guid.as_bytes()).as_bytes();
        raw.partition_array_start = self.partition_array_start;
        raw.partitions = self.partitions;
        // No need to calculate or be passed it, should be set when `self` is created.
        raw.partitions_crc32 = self.partitions_crc32;
        raw.header_crc32 = calculate_crc(raw);
        //
        let raw = &raw as *const RawHeader as *const u8;
        // Safe because we know the sizes
        let raw = unsafe { slice::from_raw_parts(raw, mem::size_of::<RawHeader>()) };
        //
        dest[..mem::size_of::<RawHeader>()].copy_from_slice(raw);
        //
        Ok(())
    }
}

use crate::mbr::ProtectiveMbr;
use generic_array::{
    typenum::{Unsigned, U128, U36},
    ArrayLength,
    GenericArray,
};

type PartitionsArray<N = U128> = GenericArray<Partition, N>;

/// Calculate partition crc32
///
/// See [`Gpt::from_bytes`] for details.
///
/// `CB` receives the filled partition buffer, which is always
/// PARTITION_ENTRY_SIZE bytes
///
/// `CB` also receives the partition number, starting at zero.
fn calculate_part_crc<F: FnMut(ByteSize, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8])>(
    func: &mut F,
    partitions: u64,
    block_size: BlockSize,
    array_start: LogicalBlockAddress,
    cb: &mut CB,
) -> Result<u32> {
    let mut digest = crc32::Digest::new(crc32::IEEE);
    let mut buf = [0; PARTITION_ENTRY_SIZE as usize];
    for i in 0..partitions {
        let b = array_start * block_size;
        let b = b + (ByteSize::from_bytes(PARTITION_ENTRY_SIZE as u64) * i);
        func(b, &mut buf)?;
        cb(i as usize, &buf);
        digest.write(&buf);
    }
    Ok(digest.sum32())
}

/// Raw partition structure
#[derive(Copy, Clone)]
#[repr(C)]
pub struct RawPartition {
    /// Defines the type of this partition
    partition_type_guid: [u8; 16],

    /// Unique identifer for this partition
    partition_guid: [u8; 16],

    /// Where it starts on disk
    starting_lba: LogicalBlockAddress,

    /// Where it ends on disk
    ending_lba: LogicalBlockAddress,

    /// Attributes
    attributes: u64,

    /// Null-terminated name, UCS-2/UTF-16LE string,
    name: GenericArray<u16, U36>,
}

/// A GPT Partition
///
/// # Examples
///
/// TODO: List all partitions on a device
#[derive(Debug, Copy, Clone, PartialEq, Default)]
pub struct Partition {
    /// Defines the type of this partition
    partition_type_guid: Uuid,

    /// Unique identifer for this partition
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

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Gpt<N = U128>
where
    N: Unsigned,
    N: ArrayLength<Partition>,
    N::ArrayType: Copy,
{
    uuid: Uuid,
    partitions: GenericArray<Partition, N>,
}

impl Gpt {
    /// Read the full GPT from byte slices
    ///
    /// `primary` must contain LBA0 and LBA1. That is, `block_size * 2` bytes.
    ///
    /// `alt` must be the last LBA. That is, `block_size` bytes.
    ///
    /// `partitions` will be called for every partition in the GPT.
    ///
    /// As an argument it receives the byte offset of the partition entry,
    /// a buffer capable of holding each partition entry.
    ///
    /// It returns a [`Result`]<()>, and errors are propagated.
    pub fn from_bytes<F: FnMut(ByteSize, &mut [u8]) -> Result<()>>(
        primary: &[u8],
        alt: &[u8],
        func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<Self> {
        Gpt::from_bytes_with_size(primary, alt, func, block_size, disk_size)
    }
}

impl<N> Gpt<N>
where
    N: Unsigned,
    N: ArrayLength<Partition>,
    N::ArrayType: Copy,
{
    /// Like [`Gpt::from_bytes`] but stores `N` partitions
    /// instead of the minimum reserved amount.
    ///
    /// Currently 16KiB bytes, or 128 partitions, is the required reserve.
    ///
    /// You probably don't want this method, but it can be useful
    /// if you're fine with only supporting a few partitions.
    ///
    /// Note that all `partitions * partition_size` bytes
    /// will still be read from the partition array, per the GPT header,
    /// this will simply cause any extras to be dropped.
    ///
    /// If you pick [`U36`] for example, and there are 40 partitions,
    /// only the first 36 partitions can be written back out.
    pub fn from_bytes_with_size<F: FnMut(ByteSize, &mut [u8]) -> Result<()>>(
        mut primary: &[u8],
        mut alt: &[u8],
        mut func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<Self> {
        let b_size = block_size.0 as usize;
        assert_eq!(primary.len(), b_size * 2, "Invalid primary");
        assert_eq!(alt.len(), b_size, "Invalid alt");
        //
        let _mbr = ProtectiveMbr::from_bytes(&mut primary, block_size)
            .map_err(|_| Error::Invalid("Invalid Protective MBR"))?;
        let primary = Header::from_bytes(&mut primary, block_size)?;
        let alt = Header::from_bytes(&mut alt, block_size)?;
        //
        let mut partitions: GenericArray<Partition, _> = Default::default();
        Gpt::validate(
            &primary,
            &alt,
            &mut func,
            block_size,
            disk_size,
            |i, source| {
                // This is okay because we use read_unaligned
                #[allow(clippy::cast_ptr_alignment)]
                let _part = unsafe { (source.as_ptr() as *const RawPartition).read_unaligned() };
                if i < partitions.len() {
                    partitions[i] = Partition::default();
                }
            },
        )?;

        Ok(Gpt {
            uuid: primary.disk_guid,
            partitions,
        })
    }
}

impl Gpt {
    fn validate<F: FnMut(ByteSize, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8])>(
        primary: &Header,
        alt: &Header,
        mut func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
        mut cb: CB,
    ) -> Result<()> {
        if primary.this_lba != LogicalBlockAddress(1) {
            return Err(Error::Invalid("Corrupt Primary GPT Header"));
        }
        let crc = calculate_part_crc(
            &mut func,
            primary.partitions as u64,
            block_size,
            primary.partition_array_start,
            &mut cb,
        )?;
        if crc != primary.partitions_crc32 {
            return Err(Error::Invalid("Primary Partition Array CRC32 mismatch"));
        }
        let last_lba = (disk_size / block_size) - 1;
        if primary.alt_lba != last_lba {
            return Err(Error::Invalid("Corrupt Primary GPT Header"));
        }
        //
        if alt.this_lba != last_lba {
            return Err(Error::Invalid("Corrupt Backup GPT Header"));
        }
        if alt.alt_lba != LogicalBlockAddress(1) {
            return Err(Error::Invalid("Corrupt Backup GPT Header"));
        }
        let crc = calculate_part_crc(
            &mut func,
            alt.partitions as u64,
            block_size,
            alt.partition_array_start,
            &mut cb,
        )?;
        if crc != alt.partitions_crc32 {
            return Err(Error::Invalid("Backup Partition Array CRC32 mismatch"));
        }
        //
        Ok(())
    }
}

#[cfg(test)]
mod tests_gpt {
    use super::*;
    use crate::partitions::PartitionType;
    use static_assertions::*;
    use std::{
        fs,
        io::{prelude::*, SeekFrom},
    };

    assert_eq_size!(RawPartition, [u8; PARTITION_ENTRY_SIZE as usize]);

    static TEST_PARTS_CF: &str = "tests/data/test_parts_cf";

    const BLOCK_SIZE: BlockSize = BlockSize(512);
    const LARGE_BLOCK_SIZE: BlockSize = BlockSize(4096);
    // 10 * 1024^2
    const TEN_MIB_BYTES: usize = 10_485_760;
    const CF_DISK_GUID: &str = "A17875FB-1D86-EE4D-8DFE-E3E8ABBCD364";
    const CF_PART_GUID: &str = "97954376-2BB6-534B-A015-DF434A94ABA2";
    const LINUX_PART_GUID: PartitionType = PartitionType::LinuxFilesystemData;

    type Result<T = ()> = anyhow::Result<T>;

    /// Read test data
    fn data() -> Result<Vec<u8>> {
        let mut data = vec![0; TEN_MIB_BYTES];
        let mut file = fs::File::open(TEST_PARTS_CF)?;
        file.read_exact(&mut data)?;
        Ok(data)
    }

    #[test]
    fn read_gpt_36_parts() -> Result {
        let block = BLOCK_SIZE.0 as usize;
        //
        let mut file = fs::File::open(TEST_PARTS_CF)?;
        let mut primary = [0; BLOCK_SIZE.0 as usize * 2];
        let mut alt = [0; BLOCK_SIZE.0 as usize];
        file.read_exact(&mut primary)?;
        file.seek(SeekFrom::End(-(block as i64)))?;
        file.read_exact(&mut alt)?;
        //
        let raw = data()?;
        let primary = &raw[..block * 2];
        let alt = &raw[raw.len() - block..];
        let _gpt: Gpt<U36> = Gpt::from_bytes_with_size(
            &primary,
            &alt,
            |i, buf| {
                let i = i.as_bytes() as usize;
                let size = buf.len();
                buf.copy_from_slice(&raw[i..][..size]);
                file.seek(SeekFrom::Start(i as u64)).unwrap();
                file.read_exact(buf).unwrap();
                Ok(())
            },
            BLOCK_SIZE,
            ByteSize::from_bytes(TEN_MIB_BYTES as u64),
        )?;
        //
        Ok(())
    }

    #[test]
    fn read_gpt() -> Result {
        let block = BLOCK_SIZE.0 as usize;
        //
        let mut file = fs::File::open(TEST_PARTS_CF)?;
        let mut primary = [0; BLOCK_SIZE.0 as usize * 2];
        let mut alt = [0; BLOCK_SIZE.0 as usize];
        file.read_exact(&mut primary)?;
        file.seek(SeekFrom::End(-(block as i64)))?;
        file.read_exact(&mut alt)?;
        //
        let raw = data()?;
        let primary = &raw[..block * 2];
        let alt = &raw[raw.len() - block..];
        let _gpt = Gpt::from_bytes(
            &primary,
            &alt,
            |i, buf| {
                let i = i.as_bytes() as usize;
                let size = buf.len();
                buf.copy_from_slice(&raw[i..][..size]);
                file.seek(SeekFrom::Start(i as u64)).unwrap();
                file.read_exact(buf).unwrap();
                Ok(())
            },
            BLOCK_SIZE,
            ByteSize::from_bytes(TEN_MIB_BYTES as u64),
        )?;
        //
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use static_assertions::*;
    use std::{fs, io::prelude::*};

    assert_eq_size!(RawHeader, [u8; 92]);

    static TEST_PARTS_CF: &str = "tests/data/test_parts_cf";

    const BLOCK_SIZE: BlockSize = BlockSize(512);
    const LARGE_BLOCK_SIZE: BlockSize = BlockSize(4096);
    // 10 * 1024^2
    const TEN_MIB_BYTES: usize = 10_485_760;
    const CF_DISK_GUID: &str = "A17875FB-1D86-EE4D-8DFE-E3E8ABBCD364";

    type Result<T = ()> = anyhow::Result<T>;

    /// Read test data
    fn data() -> Result<Vec<u8>> {
        let mut data = vec![0; TEN_MIB_BYTES];
        let mut file = fs::File::open(TEST_PARTS_CF)?;
        file.read_exact(&mut data)?;
        Ok(data)
    }

    #[test]
    fn read_write_header() -> Result {
        let raw = &data()?[BLOCK_SIZE.0 as usize..][..BLOCK_SIZE.0 as usize];
        let header = Header::from_bytes(&mut &*raw, BLOCK_SIZE)?;
        assert_eq!(
            header.disk_guid,
            Uuid::parse_str(CF_DISK_GUID).unwrap(),
            "UUID didn't match test data"
        );
        let mut written = vec![0; BLOCK_SIZE.0 as usize];
        header.to_bytes(&mut written)?;
        assert_eq!(
            written.len(),
            raw.len(),
            "Mismatch between read and written headers"
        );
        assert_eq!(written, raw, "Mismatch between read and written headers");
        //
        Ok(())
    }

    #[test]
    fn read_write_large_header() -> Result {
        let raw = &data()?[BLOCK_SIZE.0 as usize..][..BLOCK_SIZE.0 as usize];
        let header = Header::from_bytes(&mut &*raw, BLOCK_SIZE)?;
        assert_eq!(
            header.disk_guid,
            Uuid::parse_str(CF_DISK_GUID).unwrap(),
            "UUID didn't match test data"
        );
        let mut written = vec![0; LARGE_BLOCK_SIZE.0 as usize];
        header.to_bytes(&mut written)?;
        // Compare only header bytes
        let written = &written[..HEADER_SIZE as usize];
        let raw = &raw[..HEADER_SIZE as usize];
        assert_eq!(written.len(), raw.len());
        assert_eq!(written, raw);
        //
        Ok(())
    }
}
