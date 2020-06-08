//! Handle partitions
use super::{
    error::*,
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

/// Calculate partition crc32.
///
/// See [`super::Gpt::from_bytes`] for details.
///
/// `CB` receives the filled partition buffer, which is always
/// PARTITION_ENTRY_SIZE bytes
///
/// `CB` also receives the partition number, starting at zero.
pub fn calculate_part_crc<F, CB>(
    func: &mut F,
    partitions: u64,
    array_start: Offset,
    entry_size: usize,
    cb: &mut CB,
) -> Result<u32>
where
    F: FnMut(Offset, &mut [u8]) -> Result<()>,
    CB: FnMut(usize, &[u8]) -> Result<()>,
{
    let mut digest = crc32::Digest::new(crc32::IEEE);
    let mut buf = [0; PARTITION_ENTRY_SIZE as usize];
    for i in 0..partitions {
        let b = Offset(array_start.0 + ((entry_size as u64) * i));
        func(b, &mut buf)?;
        cb(i as usize, &buf)?;
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
    start: Block,

    /// Where it ends on disk
    end: Block,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Partition name, converted from UTF-16-LE
    ///
    /// Hard-coded limit of 70 bytes, last two MUST be null.
    ///
    /// Use size of 72 because it has a default impl and 70 doesn't.
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

    /// Read from bytes.
    ///
    /// Invalid characters in the partition name are replaced.
    ///
    /// # Errors
    ///
    /// - [`Error::NotEnough`] if `source` is too small
    pub(crate) fn from_bytes(source: &[u8]) -> Result<Self> {
        // SAFETY:
        // - `source` is valid for `size_of::<RawPartition>` bytes
        // - `RawPartition` is `repr(C)`
        // - `read_unaligned` is used
        let part = unsafe {
            if source.len() < mem::size_of::<RawPartition>() {
                return Err(Error::NotEnough);
            }
            #[allow(clippy::cast_ptr_alignment)]
            (source.as_ptr() as *const RawPartition).read_unaligned()
        };
        let mut name = ArrayString::new();
        decode_utf16(part.name.iter().cloned())
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .filter(|c| *c != '\0')
            .for_each(|r| {
                name.push(r);
            });
        Ok(Partition {
            partition_type: PartitionType::from_uuid(uuid_hack(part.partition_type_guid)),
            guid: uuid_hack(part.partition_guid),
            start: Block(part.starting_lba),
            end: Block(part.ending_lba),
            attributes: part.attributes,
            name,
        })
    }

    /// Write to `dest`
    ///
    /// # Errors
    ///
    /// - [`Error::NotEnough`] if `dest` is too small.
    pub(crate) fn to_bytes(&self, dest: &mut [u8]) -> Result<()> {
        let mut raw = RawPartition::default();
        raw.partition_type_guid = *uuid_hack(*self.partition_type.to_uuid().as_bytes()).as_bytes();
        raw.partition_guid = *uuid_hack(*self.guid.as_bytes()).as_bytes();
        raw.starting_lba = self.start.0;
        raw.ending_lba = self.end.0;
        raw.attributes = self.attributes;
        self.name()
            .encode_utf16()
            .enumerate()
            .for_each(|(i, c)| raw.name[i] = c);
        // SAFETY:
        // - `self` is valid and aligned.
        // - `RawPartition` is `repr(C)`
        let raw = unsafe {
            let ptr = &raw as *const RawPartition as *const u8;
            slice::from_raw_parts(ptr, mem::size_of::<RawPartition>())
        };
        dest.get_mut(..mem::size_of::<RawPartition>())
            .ok_or(Error::NotEnough)?
            .copy_from_slice(raw);
        Ok(())
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

    /// Partition starting [`Block`]
    pub fn start(&self) -> Block {
        self.start
    }

    /// Partition ending [`Block`]
    pub fn end(&self) -> Block {
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
    Abs(Block),
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
    start: Block,
    end: End,
    partition_type: PartitionType,
    uuid: Uuid,
    name: ArrayString<[u8; 72]>,
    block_size: BlockSize,
}

impl PartitionBuilder {
    /// New builder
    ///
    /// `uuid` is a unique identifer for the partition.
    ///
    /// # Panics
    ///
    /// - If `uuid` is nil.
    pub fn new(uuid: Uuid, gpt: &crate::Gpt) -> Self {
        // Testing uses nil UUID's for convenience.
        #[cfg(not(test))]
        assert!(
            !uuid.is_nil(),
            "UUID cannot be nil. Partitions MUST be uniquely identifiable."
        );
        Self {
            start: Default::default(),
            end: Default::default(),
            partition_type: Default::default(),
            uuid,
            name: Default::default(),
            block_size: gpt.block_size,
        }
    }

    /// Partition start. Required.
    pub fn start(mut self, start: Block) -> Self {
        self.start = start;
        self
    }

    /// Partition end. Required.
    ///
    /// Call one of this or [`PartitionBuilder::size`]
    pub fn end(mut self, end: Block) -> Self {
        self.end = End::Abs(end);
        self
    }

    /// Partition size. Required.
    ///
    /// Call one of this or [`PartitionBuilder::end`]
    ///
    /// # Warning
    ///
    /// Partitions can only be multiples of the Gpt [`BlockSize`],
    /// so make sure `size` is evenly divisible or it'll be round **down**.
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
        self.name.clear();
        self.name.push_str(name);
        self
    }

    /// Create Partition
    ///
    /// # Panics
    ///
    /// - If not all required methods were called.
    pub fn finish(self) -> Partition {
        let block_size = self.block_size;
        let end = match self.end {
            End::Abs(end) => end,
            End::Rel(end) => {
                // Minus block because last is inclusive.
                Block(
                    (Offset((self.start * block_size).0 + end.as_bytes()) / block_size)
                        .0
                        .checked_sub(1)
                        .expect("Invalid Partition Size"),
                )
            }
            End::None => panic!("Invalid Partition Creation: Missing size"),
        };
        Partition {
            partition_type: self.partition_type,
            guid: self.uuid,
            start: self.start,
            end,
            attributes: 0,
            name: self.name,
        }
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use pretty_assertions::assert_eq;
    use static_assertions::*;

    assert_eq_size!(RawPartition, [u8; PARTITION_ENTRY_SIZE as usize]);

    /// Skip the MBR and GPT, first partition.
    const OFFSET: usize = (BLOCK_SIZE.get() * 2) as usize;

    #[test]
    fn read_part() -> Result {
        let raw = data()?;
        let raw = &raw[OFFSET..];
        let part = Partition::from_bytes(raw)?;
        assert_eq!(part.partition_type(), PartitionType::LinuxFilesystemData);
        Ok(())
    }

    #[test]
    fn part_roundtrip() -> Result {
        let raw = data_parted()?;
        let raw = &raw[OFFSET..];
        let part = Partition::from_bytes(raw)?;
        assert_eq!("Test", part.name());
        let mut new_raw = [0; PARTITION_ENTRY_SIZE as usize];
        part.to_bytes(&mut new_raw)?;
        assert_eq!(&new_raw[..], &raw[..PARTITION_ENTRY_SIZE as usize]);
        Ok(())
    }

    #[test]
    fn create_part() -> Result {
        let raw = data()?;
        let raw_part = &raw[OFFSET..][..PARTITION_ENTRY_SIZE as usize];
        let part = PartitionBuilder::new(
            Uuid::parse_str(CF_PART_GUID)?,
            &crate::Gpt::new(Uuid::nil(), Size::from_mib(1), BlockSize::new(512)),
        )
        .start(Size::from_mib(1) / BLOCK_SIZE)
        .size(Size::from_mib(8))
        .partition_type(PartitionType::LinuxFilesystemData)
        .finish();
        let mut buf = [0; PARTITION_ENTRY_SIZE as usize];
        part.to_bytes(&mut buf)?;
        //
        let new = Partition::from_bytes(&buf)?;
        let old = Partition::from_bytes(&raw_part)?;
        dbg!(new);
        dbg!(old);
        //
        assert_eq!(new.start(), old.start());
        assert_eq!(new.end(), old.end());
        assert_eq!(buf.len(), raw_part.len());
        assert_eq!(&buf[..], raw_part);
        //
        Ok(())
    }

    #[test]
    fn part_name_emoji() -> Result {
        let mut raw = [0; PARTITION_ENTRY_SIZE as usize];
        // Because I was eating pizza when I wrote this.
        let name = "🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕🍕!!";
        assert_eq!(name.len(), 70);
        let mut raw_name = [0; 72];
        raw_name[..name.len()].clone_from_slice(name.as_bytes());
        //
        let part = PartitionBuilder::new(
            Uuid::nil(),
            &crate::Gpt::new(Uuid::nil(), Size::from_mib(1), BlockSize::new(512)),
        )
        .start(Block(34))
        .end(Block(35))
        .partition_type(PartitionType::Unused)
        .name(name)
        .finish();
        assert_eq!(name, part.name());
        part.to_bytes(&mut raw)?;
        //
        let part = Partition::from_bytes(&raw)?;
        assert_eq!(name, part.name());
        Ok(())
    }
}
