//! Handle GPT header
use super::{error::*, partition::MIN_PARTITIONS_BYTES};
use crate::types::*;
use core::{convert::TryInto, mem, slice};
use crc::crc32;
use uuid::Uuid;

/// "EFI PART" constant as a u64
const EFI_PART: u64 = 0x5452_4150_2049_4645;

/// Current/supported GPT Header revision
const REVISION: u32 = 0x0001_0000;

/// Current/supported GPT Header size.
///
/// Only used when writing, can in theory read and validate larger headers.
pub const HEADER_SIZE: u32 = 92;

/// Current/supported GPT Partition Entry size.
///
/// Only used when writing, can in theory read and validate larger entries.
pub const PARTITION_ENTRY_SIZE: u32 = 128;

/// GPT stores UUID's in big endian, but with the time* fields as little endian.
///
/// See Appendix A for more details.
pub fn uuid_hack(uuid: [u8; 16]) -> Uuid {
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
    pub this: LogicalBlockAddress,

    /// The logical block address the backup header is in
    pub alt: LogicalBlockAddress,

    /// First valid LBA for partitions
    pub first_usable: LogicalBlockAddress,

    /// Last valid LBA for partitions
    pub last_usable: LogicalBlockAddress,

    /// Disk GUID
    pub uuid: Uuid,

    /// Number of partitions
    pub partitions: u32,

    /// Where the partition array starts on disk.
    pub array: LogicalBlockAddress,

    /// CRC32 of the partition array
    pub partitions_crc32: u32,

    /// Size of each partition entry structure.
    /// Must be 128 * 2^n, where n >= 0
    pub partition_size: u32,
}

impl Header {
    pub fn new(
        this: LogicalBlockAddress,
        alt: LogicalBlockAddress,
        partitions: u32,
        partitions_crc32: u32,
        disk_uuid: Uuid,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Self {
        let array_size = LogicalBlockAddress(MIN_PARTITIONS_BYTES / block_size.0);
        let last = (disk_size / block_size) - 1;
        Self {
            this,
            alt,
            // Partition array, plus the MBR and GPT header
            first_usable: array_size + 2,
            // Partition array, minus GPT header
            last_usable: last - array_size - 1,
            uuid: disk_uuid,
            partitions,
            //
            array: if this.0 == 1 {
                LogicalBlockAddress(2)
            } else {
                last - array_size
            },
            partitions_crc32,
            partition_size: PARTITION_ENTRY_SIZE,
        }
    }
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
            this: raw.this_lba,
            alt: raw.alt_lba,
            first_usable: raw.first_usable_lba,
            last_usable: raw.last_usable_lba,
            uuid: uuid_hack(raw.disk_guid),
            partitions: raw.partitions,
            array: raw.partition_array_start,
            partitions_crc32: raw.partitions_crc32,
            partition_size: raw.partition_size,
        };
        *source = &source[b_size..];
        Ok(header)
    }

    /// Write the GPT header to `dest`
    pub fn to_bytes(&self, dest: &mut [u8]) -> Result<()> {
        let mut raw = RawHeader::default();
        raw.this_lba = self.this;
        raw.alt_lba = self.alt;
        raw.first_usable_lba = self.first_usable;
        raw.last_usable_lba = self.last_usable;
        raw.disk_guid = *uuid_hack(*self.uuid.as_bytes()).as_bytes();
        raw.partition_array_start = self.array;
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
            header.uuid,
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
            header.uuid,
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
