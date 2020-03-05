//! Handle partitions
use super::{
    error::Result,
    header::{uuid_hack, PARTITION_ENTRY_SIZE},
};
use crate::{partitions::PartitionType, types::*};
use core::{
    char::{decode_utf16, REPLACEMENT_CHARACTER},
    mem,
    slice,
    str::from_utf8,
};
use crc::{crc32, Hasher32};
use generic_array::{
    typenum::{U36, U70},
    GenericArray,
};
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
// We can't fix that until [#91][1] is fixed though
// Maybe `mem::zeroed`?
// [1]: https://github.com/fizyk20/generic-array/issues/91
#[derive(Debug, Copy, Clone, PartialEq, Default)]
pub struct Partition {
    /// Defines the type of this partition
    partition_type: PartitionType,

    /// Unique identifer for this partition
    guid: Uuid,

    /// Where it starts on disk
    start: LogicalBlockAddress,

    /// Where it ends on disk
    end: LogicalBlockAddress,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Partition name, converted from UTF-16-LE
    /// U70 because null-terminated, we don't need the null.
    name: GenericArray<u8, U70>,
}

impl Partition {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_bytes(source: &[u8]) -> Self {
        #[allow(clippy::cast_ptr_alignment)]
        let part = unsafe { (source.as_ptr() as *const RawPartition).read_unaligned() };
        let mut name: GenericArray<u8, U70> = Default::default();
        let mut offset = 0;
        decode_utf16(part.name)
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .for_each(|r| {
                r.encode_utf8(&mut name[offset..]);
                offset += r.len_utf8();
            });
        Partition {
            partition_type: PartitionType::from_uuid(uuid_hack(part.partition_type_guid)),
            guid: uuid_hack(part.partition_guid),
            start: part.starting_lba,
            end: part.ending_lba,
            attributes: part.attributes,
            name,
        }
    }

    pub(crate) fn to_bytes(&self, dest: &mut [u8]) {
        let mut raw = RawPartition::default();
        raw.partition_type_guid = *uuid_hack(*self.partition_type.to_uuid().as_bytes()).as_bytes();
        raw.partition_guid = *uuid_hack(*self.guid.as_bytes()).as_bytes();
        raw.starting_lba = self.start;
        raw.ending_lba = self.end;
        raw.attributes = self.attributes;
        self.name()
            .encode_utf16()
            .enumerate()
            .for_each(|(i, c)| raw.name[i] = c);
        //
        let raw = &raw as *const RawPartition as *const u8;
        // Safe because we know the sizes
        let raw = unsafe { slice::from_raw_parts(raw, mem::size_of::<RawPartition>()) };
        dest[..mem::size_of::<RawPartition>()].copy_from_slice(raw);
    }
}

impl Partition {
    pub fn name(&self) -> &str {
        from_utf8(&self.name)
            .unwrap()
            .trim_end_matches(|c| c == '\0')
    }

    pub fn partition_type(&self) -> PartitionType {
        self.partition_type
    }

    pub fn uuid(&self) -> Uuid {
        self.guid
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use static_assertions::*;

    assert_eq_size!(RawPartition, [u8; PARTITION_ENTRY_SIZE as usize]);

    const OFFSET: usize = (BLOCK_SIZE.0 * 2) as usize;

    #[test]
    fn read_part() -> Result {
        let raw = data()?;
        let raw = &raw[OFFSET..];
        let part = Partition::from_bytes(raw);
        assert_eq!(part.partition_type(), PartitionType::LinuxFilesystemData);
        Ok(())
    }

    #[test]
    fn part_roundtrip() -> Result {
        let raw = data_parted()?;
        // Skip MBR and GPT header, first partition is there.
        let raw = &raw[OFFSET..];
        let part = Partition::from_bytes(raw);
        assert_eq!("Test", part.name());
        let mut new_raw = [0; PARTITION_ENTRY_SIZE as usize];
        part.to_bytes(&mut new_raw);
        assert_eq!(&new_raw[..], &raw[..PARTITION_ENTRY_SIZE as usize]);
        Ok(())
    }

    #[test]
    fn part_name_emoji() {
        let mut raw = [0; PARTITION_ENTRY_SIZE as usize];
        // Because I was eating pizza when I wrote this.
        let name = "🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕!!";
        assert_eq!(name.len(), 70);
        let mut raw_name = [0; 70];
        raw_name[..name.len()].clone_from_slice(name.as_bytes());
        let part = Partition {
            partition_type: PartitionType::Unused,
            guid: Uuid::nil(),
            start: LogicalBlockAddress(0),
            end: LogicalBlockAddress(0),
            attributes: 0,
            name: *GenericArray::from_slice(&raw_name),
        };
        assert_eq!(name, part.name());
        part.to_bytes(&mut raw);
        //
        let part = Partition::from_bytes(&raw);
        assert_eq!(name, part.name());
    }
}
