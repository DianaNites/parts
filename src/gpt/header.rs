//! Handle GPT header
use super::error::*;
use crate::types::*;
use core::{mem, slice};
use crc::{crc32, Hasher32};
use uuid::Uuid;

/// A minimum of 16,384 bytes are reserved for the partition array.
///
/// With current GPT Partition entry sizes this means a minimum of 128
/// partitions
const MIN_PARTITIONS_BYTES: Size = Size::from_bytes(16384);

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
///
/// See https://github.com/uuid-rs/uuid/issues/462
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
///
/// `extra` is all bytes in the rest of the block, if any.
fn calculate_crc(mut header: RawHeader, extra: &[u8]) -> u32 {
    header.header_crc32 = 0;
    // SAFETY:
    // - `&header` is valid and aligned
    // - `RawHeader` is repr(C, packed)
    let source_bytes = unsafe {
        slice::from_raw_parts(
            (&header as *const _) as *const u8,
            mem::size_of::<RawHeader>(),
        )
    };
    let mut digest = crc32::Digest::new(crc32::IEEE);
    // Header bytes
    digest.write(&source_bytes[..HEADER_SIZE as usize]);
    // Any extra. Shouldn't change the result if passed an empty slice?
    let size = (header.header_size - HEADER_SIZE) as usize;
    digest.write(&extra[..size]);
    digest.sum32()
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
    this_lba: u64,

    /// The logical block address the backup header is in
    alt_lba: u64,

    /// Where partitions can start
    first_usable_lba: u64,

    /// Where partitions must end
    last_usable_lba: u64,

    /// Disk GUID. See [`uuid_hack`] for details.
    disk_guid: [u8; 16],

    /// Where our partition array starts on disk.
    partition_array_start: u64,

    /// Number of partitions
    partitions: u32,

    /// Size of each partition entry structure.
    /// Must be 128 * 2^n, where n >= 0
    partition_size: u32,

    /// CRC32 of the partition array
    partitions_crc32: u32,
}

/// A minimally "valid" Default for `RawHeader`.
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

/// Header kind
pub enum HeaderKind {
    Primary,
    Backup,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Header {
    /// The logical block address this header is in
    pub this: Block,

    /// The logical block address the backup header is in
    pub alt: Block,

    /// First valid LBA for partitions
    pub first_usable: Block,

    /// Last valid LBA for partitions
    pub last_usable: Block,

    /// Disk GUID
    pub uuid: Uuid,

    /// Number of partitions
    pub partitions: u32,

    /// Where the partition array starts on disk.
    pub array: Block,

    /// CRC32 of the partition array
    pub partitions_crc32: u32,

    /// Partition Entry Size
    pub entry_size: u32,
}

impl Header {
    /// `partitions` MUST be the >= 128.
    /// parted, cfdisk, and presumably others will CRASH if this is not the
    /// case.
    ///
    /// `partitions_crc32` MUST be calculated over this range,
    /// even if all zeros
    pub fn new(
        kind: HeaderKind,
        partitions: u32,
        partitions_crc32: u32,
        disk_uuid: Uuid,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Self {
        let (first_usable, last_usable) = Header::usable(block_size, disk_size);
        // Account for array
        let alt = last_usable + 1 + (MIN_PARTITIONS_BYTES / block_size).0;
        //
        Self {
            this: match kind {
                HeaderKind::Primary => Block(1),
                HeaderKind::Backup => alt,
            },
            alt: match kind {
                HeaderKind::Primary => alt,
                HeaderKind::Backup => Block(1),
            },
            first_usable,
            last_usable,
            uuid: disk_uuid,
            partitions,
            //
            array: match kind {
                HeaderKind::Primary => Block(2),
                HeaderKind::Backup => last_usable + 1,
            },
            partitions_crc32,
            entry_size: PARTITION_ENTRY_SIZE,
        }
    }

    /// Returns first and last usable LBA
    pub fn usable(block_size: BlockSize, disk_size: Size) -> (Block, Block) {
        let array_end: Block = MIN_PARTITIONS_BYTES / block_size;
        let last: Block = (disk_size / block_size) - 1;
        ((array_end + 2), (last - array_end.0 - 1))
    }
}

impl Header {
    /// Read the GPT Header from a byte slice
    ///
    /// # Errors
    ///
    /// - The GPT is invalid.
    /// - [`Error::NotEnough`] if `source` is not `block_size` bytes
    pub fn from_bytes(source: &[u8], block_size: BlockSize) -> Result<Self> {
        if source.len() < mem::size_of::<RawHeader>() {
            return Err(Error::NotEnough);
        }
        // SAFETY:
        // - `source` is valid for `size_of::<RawHeader>` bytes
        // - `size_of::<RawHeader>` is less than `block_size`
        // - `RawHeader` is `repr(C, packed)`
        // - `read_unaligned` is used
        let raw = unsafe { (source.as_ptr() as *const RawHeader).read_unaligned() };
        if raw.signature != EFI_PART {
            return Err(Error::Invalid("Invalid Signature"));
        }
        // See [`RawHeader::header_size`]
        if raw.header_size < HEADER_SIZE || raw.header_size as u64 > block_size.get() {
            return Err(Error::Invalid(
                "Header size invalid, less than 92 or bigger than the block size",
            ));
        }
        if raw.header_crc32 != calculate_crc(raw, &source[HEADER_SIZE as usize..]) {
            return Err(Error::Invalid("CRC mismatch"));
        }
        let header = Header {
            this: Block(raw.this_lba),
            alt: Block(raw.alt_lba),
            first_usable: Block(raw.first_usable_lba),
            last_usable: Block(raw.last_usable_lba),
            uuid: uuid_hack(raw.disk_guid),
            partitions: raw.partitions,
            array: Block(raw.partition_array_start),
            partitions_crc32: raw.partitions_crc32,
            entry_size: raw.partition_size,
        };
        Ok(header)
    }

    /// Write the GPT header to `dest`
    ///
    /// # Errors
    ///
    /// - [`Error::NotEnough`] if `dest` can't fit the header.
    pub fn to_bytes(&self, dest: &mut [u8]) -> Result<()> {
        let mut raw = RawHeader::default();
        raw.this_lba = self.this.0;
        raw.alt_lba = self.alt.0;
        raw.first_usable_lba = self.first_usable.0;
        raw.last_usable_lba = self.last_usable.0;
        raw.disk_guid = *uuid_hack(*self.uuid.as_bytes()).as_bytes();
        raw.partition_array_start = self.array.0;
        raw.partitions = self.partitions;
        // No need to calculate or be passed it, should be set when `self` is created.
        raw.partitions_crc32 = self.partitions_crc32;
        raw.header_crc32 = calculate_crc(raw, &[]);
        // SAFETY:
        // - `self` is valid and aligned.
        // - `RawHeader` is `repr(C, packed)`
        let raw = unsafe {
            let ptr = &raw as *const RawHeader as *const u8;
            slice::from_raw_parts(ptr, mem::size_of::<RawHeader>())
        };
        //
        dest.get_mut(..mem::size_of::<RawHeader>())
            .ok_or(Error::NotEnough)?
            .copy_from_slice(raw);
        Ok(())
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use pretty_assertions::assert_eq;
    use static_assertions::*;

    assert_eq_size!(RawHeader, [u8; HEADER_SIZE as usize]);

    #[test]
    fn round_trip() -> Result {
        let raw = data()?;
        let raw_primary = &raw[BLOCK_SIZE.get() as usize..][..BLOCK_SIZE.get() as usize];
        let parsed_raw_primary = Header::from_bytes(raw_primary, BLOCK_SIZE)?;
        //
        let mut raw_parsed_raw_primary = [0u8; HEADER_SIZE as usize];
        parsed_raw_primary.to_bytes(&mut raw_parsed_raw_primary)?;
        //
        assert_eq!(
            &raw_parsed_raw_primary[..],
            &raw_primary[..HEADER_SIZE as usize]
        );
        //
        Ok(())
    }

    #[test]
    fn exact_bytes() -> Result {
        let raw = data()?;
        let raw_primary = &raw[BLOCK_SIZE.get() as usize..][..BLOCK_SIZE.get() as usize];
        let raw_backup = &raw[raw.len() - 512..];
        //
        let mut my_primary = Header::new(
            HeaderKind::Primary,
            128,         // CFDisk always sets partitions to 128
            439_418_962, // Expected partition CRC32
            Uuid::parse_str(CF_DISK_GUID).unwrap(),
            BLOCK_SIZE,
            Size::from_bytes(TEN_MIB_BYTES as u64),
        );
        let mut my_backup = Header::new(
            HeaderKind::Backup,
            128,         // CFDisk always sets partitions to 128
            439_418_962, // Expected partition CRC32
            Uuid::parse_str(CF_DISK_GUID).unwrap(),
            BLOCK_SIZE,
            Size::from_bytes(TEN_MIB_BYTES as u64),
        );
        // CFDisk always uses 2048/1MiB as the first usable block
        my_primary.first_usable = Block(2048);
        my_backup.first_usable = Block(2048);
        //
        let mut raw_my_primary = [0u8; BLOCK_SIZE.get() as usize];
        let mut raw_my_backup = [0u8; BLOCK_SIZE.get() as usize];
        my_primary.to_bytes(&mut raw_my_primary[..HEADER_SIZE as usize])?;
        my_backup.to_bytes(&mut raw_my_backup[..HEADER_SIZE as usize])?;
        //
        assert_eq!(&raw_my_primary[..], &raw_primary[..]);
        //
        let parsed_raw_my_backup = Header::from_bytes(&raw_my_backup, BLOCK_SIZE)?;
        let parsed_raw_backup = Header::from_bytes(&raw_backup, BLOCK_SIZE)?;
        dbg!(parsed_raw_my_backup.this);
        dbg!(parsed_raw_backup.this);
        //
        assert_eq!(&raw_my_backup[..], &raw_backup[..]);
        //
        Ok(())
    }

    #[test]
    fn read_write_header() -> Result {
        let raw = &data()?[BLOCK_SIZE.get() as usize..][..BLOCK_SIZE.get() as usize];
        let header = Header::from_bytes(raw, BLOCK_SIZE).map_err(anyhow::Error::msg)?;
        assert_eq!(
            header.uuid,
            Uuid::parse_str(CF_DISK_GUID).unwrap(),
            "UUID didn't match test data"
        );
        let mut written = vec![0; BLOCK_SIZE.get() as usize];
        header.to_bytes(&mut written[..HEADER_SIZE as usize])?;
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
        let raw = &data()?[BLOCK_SIZE.get() as usize..][..BLOCK_SIZE.get() as usize];
        let header = Header::from_bytes(raw, BLOCK_SIZE).map_err(anyhow::Error::msg)?;
        assert_eq!(
            header.uuid,
            Uuid::parse_str(CF_DISK_GUID).unwrap(),
            "UUID didn't match test data"
        );
        let mut written = vec![0; LARGE_BLOCK_SIZE.get() as usize];
        header.to_bytes(&mut written[..HEADER_SIZE as usize])?;
        // Compare only header bytes
        let written = &written[..HEADER_SIZE as usize];
        let raw = &raw[..HEADER_SIZE as usize];
        assert_eq!(written.len(), raw.len());
        assert_eq!(written, raw);
        //
        Ok(())
    }
}
