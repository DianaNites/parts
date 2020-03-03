//! Handle partitions
use super::{
    error::Result,
    header::{uuid_hack, PARTITION_ENTRY_SIZE},
};
use crate::types::*;
use core::{mem, slice};
use crc::{crc32, Hasher32};
use generic_array::{typenum::U36, GenericArray};
use uuid::Uuid;

/// A minimum of 16,384 bytes are reserved for the partition array.
///
/// With current GPT Partition entry sizes this means a minimum of 128
/// partitions
pub const MIN_PARTITIONS_BYTES: u64 = 16384;

/// Calculate partition crc32
///
/// See [`Gpt::from_bytes`] for details.
///
/// `CB` receives the filled partition buffer, which is always
/// PARTITION_ENTRY_SIZE bytes
///
/// `CB` also receives the partition number, starting at zero.
pub fn calculate_part_crc<F: FnMut(ByteSize, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8])>(
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
#[derive(Copy, Clone, Default)]
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
// FIXME: Default is not a valid partition, this is public API, don't derive it.
#[derive(Debug, Copy, Clone, PartialEq, Default)]
pub struct Partition {
    /// Defines the type of this partition
    partition_type: Uuid,

    /// Unique identifer for this partition
    guid: Uuid,

    /// Where it starts on disk
    start: LogicalBlockAddress,

    /// Where it ends on disk
    end: LogicalBlockAddress,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Null-terminated name, UCS-2/UTF-16LE string,
    name: GenericArray<u16, U36>,
}

impl Partition {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_bytes(source: &[u8]) -> Self {
        #[allow(clippy::cast_ptr_alignment)]
        let part = unsafe { (source.as_ptr() as *const RawPartition).read_unaligned() };
        Partition {
            partition_type: uuid_hack(part.partition_type_guid),
            guid: uuid_hack(part.partition_guid),
            start: part.starting_lba,
            end: part.ending_lba,
            attributes: part.attributes,
            name: part.name,
        }
    }

    pub(crate) fn to_bytes(&self, dest: &mut [u8]) {
        let mut raw = RawPartition::default();
        raw.partition_type_guid = *uuid_hack(*self.partition_type.as_bytes()).as_bytes();
        raw.partition_guid = *uuid_hack(*self.guid.as_bytes()).as_bytes();
        raw.starting_lba = self.start;
        raw.ending_lba = self.end;
        raw.attributes = self.attributes;
        raw.name = self.name;
        //
        let raw = &raw as *const RawPartition as *const u8;
        // Safe because we know the sizes
        let raw = unsafe { slice::from_raw_parts(raw, mem::size_of::<RawPartition>()) };
        dest[..mem::size_of::<RawPartition>()].copy_from_slice(raw);
    }
}

impl Partition {
    pub fn uuid(&self) -> Uuid {
        self.guid
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use static_assertions::*;

    assert_eq_size!(RawPartition, [u8; PARTITION_ENTRY_SIZE as usize]);

    #[test]
    #[ignore]
    fn read_part() {
        todo!()
    }
}
