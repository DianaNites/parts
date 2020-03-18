//! Handle partitions
use super::{
    error::Result,
    header::{uuid_hack, PARTITION_ENTRY_SIZE},
};
use crate::{partitions::PartitionType, types::*};
use arrayvec::ArrayString;
use core::{
    char::{decode_utf16, REPLACEMENT_CHARACTER},
    fmt,
    mem,
    slice,
};
use crc::{crc32, Hasher32};
use uuid::Uuid;

/// A minimum of 16,384 bytes are reserved for the partition array.
///
/// With current GPT Partition entry sizes this means a minimum of 128
/// partitions
pub const MIN_PARTITIONS_BYTES: u64 = 16384;

/// Calculate partition crc32
///
/// See [`super::Gpt::from_bytes`] for details.
///
/// `CB` receives the filled partition buffer, which is always
/// PARTITION_ENTRY_SIZE bytes
///
/// `CB` also receives the partition number, starting at zero.
pub fn calculate_part_crc<F: FnMut(Offset, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8])>(
    func: &mut F,
    partitions: u64,
    array_start: Offset,
    cb: &mut CB,
) -> Result<u32> {
    let mut digest = crc32::Digest::new(crc32::IEEE);
    let mut buf = [0; PARTITION_ENTRY_SIZE as usize];
    for i in 0..partitions {
        let b = Offset(array_start.0 + ((PARTITION_ENTRY_SIZE as u64) * i));
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
    starting_lba: u64,

    /// Where it ends on disk
    ending_lba: u64,

    /// Attributes
    attributes: u64,

    /// Null-terminated name, UCS-2/UTF-16LE string,
    name: [u16; 36],
}

impl Default for RawPartition {
    fn default() -> Self {
        Self {
            partition_type_guid: Default::default(),
            partition_guid: Default::default(),
            starting_lba: Default::default(),
            ending_lba: Default::default(),
            attributes: Default::default(),
            name: [0; 36],
        }
    }
}

/// A GPT Partition
///
/// # Examples
///
/// TODO: List all partitions on a device
#[derive(Copy, Clone, PartialEq)]
pub struct Partition {
    /// Defines the type of this partition
    partition_type: PartitionType,

    /// Unique identifer for this partition
    guid: Uuid,

    /// Where it starts on disk
    start: Offset,

    /// Where it ends on disk
    end: Offset,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Partition name, converted from UTF-16-LE
    ///
    /// Hard-coded limit of 70 bytes, last two MUST be null
    name: ArrayString<[u8; 72]>,
}

impl Partition {
    pub(crate) fn new() -> Self {
        Self {
            partition_type: Default::default(),
            guid: Default::default(),
            start: Default::default(),
            end: Default::default(),
            attributes: Default::default(),
            name: Default::default(),
        }
    }

    pub(crate) fn from_bytes(source: &[u8], block_size: BlockSize) -> Self {
        #[allow(clippy::cast_ptr_alignment)]
        let part = unsafe { (source.as_ptr() as *const RawPartition).read_unaligned() };
        let mut name = ArrayString::new();
        decode_utf16(part.name.iter().cloned())
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .filter(|c| *c != '\0')
            .for_each(|r| {
                name.push(r);
            });
        Partition {
            partition_type: PartitionType::from_uuid(uuid_hack(part.partition_type_guid)),
            guid: uuid_hack(part.partition_guid),
            start: Block::new(part.starting_lba, block_size).into_offset(),
            end: Block::new(part.ending_lba, block_size).into_offset(),
            attributes: part.attributes,
            name,
        }
    }

    pub(crate) fn to_bytes(&self, dest: &mut [u8], block_size: BlockSize) {
        let mut raw = RawPartition::default();
        raw.partition_type_guid = *uuid_hack(*self.partition_type.to_uuid().as_bytes()).as_bytes();
        raw.partition_guid = *uuid_hack(*self.guid.as_bytes()).as_bytes();
        raw.starting_lba = (self.start / block_size).into();
        raw.ending_lba = (self.end / block_size).into();
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
    /// Partition name.
    // TODO: Use Option?
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Partition type
    pub fn partition_type(&self) -> PartitionType {
        self.partition_type
    }

    /// Unique identifer for this Partition
    pub fn uuid(&self) -> Uuid {
        self.guid
    }

    /// Partition starting offset
    pub fn start(&self) -> Offset {
        self.start
    }

    /// Partition ending offset
    pub fn end(&self) -> Offset {
        self.end
    }
}

impl fmt::Debug for Partition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Partition")
            .field("partition_type", &self.partition_type)
            .field("uuid", &self.guid)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("attributes", &self.attributes)
            .field("name", &self.name())
            .finish()
    }
}

#[derive(Debug, Copy, Clone)]
enum End {
    None,
    Abs(Offset),
    Rel(Size),
}

impl Default for End {
    fn default() -> Self {
        Self::None
    }
}

/// Create a Partition
#[derive(Copy, Clone)]
pub struct PartitionBuilder {
    start: Offset,
    end: End,
    partition_type: PartitionType,
    uuid: Uuid,
    name: [u8; 72],
}

impl PartitionBuilder {
    /// New builder
    ///
    /// `uuid` is a unique identifer for the partition.
    pub fn new(uuid: Uuid) -> Self {
        Self {
            start: Default::default(),
            end: Default::default(),
            partition_type: Default::default(),
            uuid,
            name: [0; 72],
        }
    }

    /// Partition start. Required.
    pub fn start(mut self, start: Offset) -> Self {
        self.start = start;
        self
    }

    /// Partition end. Required.
    ///
    /// Call one of this or [`PartitionBuilder::size`]
    pub fn end(mut self, end: Offset) -> Self {
        self.end = End::Abs(end);
        self
    }

    /// Partition size. Required.
    ///
    /// Call one of this or [`PartitionBuilder::end`]
    ///
    /// This size will be rounded up to nearest block_size
    pub fn size(mut self, size: Size) -> Self {
        self.end = End::Rel(size);
        self
    }

    /// Partition type. Required.
    pub fn partition_type(mut self, p_type: PartitionType) -> Self {
        self.partition_type = p_type;
        self
    }

    /// Partition name.
    ///
    /// # Panics
    ///
    /// - If name is more than 70 bytes.
    pub fn name(mut self, name: &str) -> Self {
        assert!(name.len() <= 70);
        self.name[..name.len()].copy_from_slice(name.as_bytes());
        self
    }

    /// Create Partition
    ///
    /// # Panics
    ///
    /// - If not all required methods were called.
    /// - If the size is not at least `block_size`
    pub fn finish(self, block_size: BlockSize) -> Partition {
        let end = match self.end {
            End::Abs(end) => end,
            End::Rel(end) => Offset(self.start.0 + end.as_bytes()),
            End::None => panic!("Invalid Partition Creation"),
        };
        // Because last block is inclusive.
        let mut end = Offset(
            end.0
                .checked_sub(block_size.0)
                .expect("Invalid Partition Size"),
        );
        // Round up
        let e = end.0 % block_size.0;
        if e != 0 {
            end = Offset(end.0 + (block_size.0 - e));
        }
        let mut name = ArrayString::from_byte_string(&self.name).unwrap();
        // Need to remove null bytes
        name.truncate(core::cmp::min(
            self.name.iter().filter(|c| **c != b'\0').count(),
            70,
        ));
        Partition {
            partition_type: self.partition_type,
            guid: self.uuid,
            start: self.start,
            end,
            attributes: 0,
            name,
        }
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
        let part = Partition::from_bytes(raw, BLOCK_SIZE);
        assert_eq!(part.partition_type(), PartitionType::LinuxFilesystemData);
        Ok(())
    }

    #[test]
    fn part_roundtrip() -> Result {
        let raw = data_parted()?;
        // Skip MBR and GPT header, first partition is there.
        let raw = &raw[OFFSET..];
        let part = Partition::from_bytes(raw, BLOCK_SIZE);
        assert_eq!("Test", part.name());
        let mut new_raw = [0; PARTITION_ENTRY_SIZE as usize];
        part.to_bytes(&mut new_raw, BLOCK_SIZE);
        assert_eq!(&new_raw[..], &raw[..PARTITION_ENTRY_SIZE as usize]);
        Ok(())
    }

    #[test]
    fn part_name_emoji() {
        let mut raw = [0; PARTITION_ENTRY_SIZE as usize];
        // Because I was eating pizza when I wrote this.
        let name = "🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕!!";
        assert_eq!(name.len(), 70);
        let mut raw_name = [0; 72];
        raw_name[..name.len()].clone_from_slice(name.as_bytes());
        //
        let part = PartitionBuilder::new(Uuid::nil())
            .start(Offset(0))
            .end(Offset(BLOCK_SIZE.0))
            .partition_type(PartitionType::Unused)
            .name(name)
            .finish(BLOCK_SIZE);
        assert_eq!(name, part.name());
        part.to_bytes(&mut raw, BLOCK_SIZE);
        //
        let part = Partition::from_bytes(&raw, BLOCK_SIZE);
        assert_eq!(name, part.name());
    }
}
