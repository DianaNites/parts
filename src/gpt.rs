//! Raw Gpt stuff
use self::{error::*, header::*, partition::*};
use crate::{
    mbr::{ProtectiveMbr, MBR_SIZE},
    types::*,
};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use arrayvec::{Array, ArrayVec};
use core::convert::TryInto;
use crc::{crc32, Hasher32};
#[cfg(feature = "std")]
use std::io::{prelude::*, SeekFrom};
use uuid::Uuid;

pub mod error;
mod header;
pub mod partition;

/// Validate the Gpt Headers.
///
/// Calls `cb` when going through the primary partition array.
/// This is used to add partitions in `GptC`
///
/// Per the GPT Spec this checks:
///
/// - The signature (Checked in [`Header::from_bytes`])
/// - Header CRC (Checked in [`Header::from_bytes`])
/// - [`Header::this`]
/// - Partition CRC
/// - For the primary, [`Header::alt`]
fn validate<F: FnMut(Offset, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8]) -> Result<()>>(
    primary: &Header,
    alt: &Header,
    mut func: F,
    block_size: BlockSize,
    disk_size: Size,
    mut cb: CB,
) -> Result<()> {
    if primary.this != Block(1) {
        return Err(Error::Invalid("Primary header location invalid"));
    }
    let crc = calculate_part_crc(
        &mut func,
        primary.partitions as u64,
        primary.array * block_size,
        primary.entry_size as usize,
        &mut cb,
    )?;
    if crc != primary.partitions_crc32 {
        return Err(Error::Invalid("Primary Partition Array CRC32 mismatch"));
    }
    let last_lba = (disk_size / block_size) - 1;
    if primary.alt != last_lba {
        return Err(Error::Invalid("Primary header alternate location invalid"));
    }
    //
    if alt.this != last_lba {
        return Err(Error::Invalid("Corrupt Backup GPT Header"));
    }
    if alt.alt != Block(1) {
        return Err(Error::Invalid("Corrupt Backup GPT Header"));
    }
    let crc = calculate_part_crc(
        &mut func,
        alt.partitions as u64,
        alt.array * block_size,
        alt.entry_size as usize,
        &mut |_, _| Ok(()),
    )?;
    if crc != alt.partitions_crc32 {
        return Err(Error::Invalid("Backup Partition Array CRC32 mismatch"));
    }
    //
    Ok(())
}

/// Helper trait for [`GptC`].
///
/// You shouldn't need to worry about this.
///
/// This is used to allow [`GptC`] to be generic over the container,
/// supporting both `std` and `no_std`, without exposing weird trait bounds to
/// the user.
pub trait GptHelper<Container> {
    /// Create a new `Container`
    fn new() -> Container;

    /// Get a slice of [`Partition`]s from `Container`
    fn as_slice(&self) -> &[Partition];

    /// Get a mutable slice of [`Partition`]s from `Container`
    fn as_mut_slice(&mut self) -> &mut [Partition];

    /// Add a [`Partition`] to the `Container`. Failable.
    fn push(&mut self, part: Partition) -> Result<()>;

    /// Remove and return the [`Partition`] at `index` from the `Container`.
    fn remove(&mut self, index: usize) -> Partition;
}

/// Support [`ArrayVec`] for `no_std`
impl<N: Array<Item = Partition>> GptHelper<ArrayVec<N>> for ArrayVec<N> {
    fn new() -> ArrayVec<N> {
        ArrayVec::new()
    }

    fn as_slice(&self) -> &[Partition] {
        self.as_slice()
    }

    fn as_mut_slice(&mut self) -> &mut [Partition] {
        self.as_mut_slice()
    }

    fn push(&mut self, part: Partition) -> Result<()> {
        self.try_push(part).map_err(|_| Error::NotEnough)
    }

    fn remove(&mut self, index: usize) -> Partition {
        self.remove(index)
    }
}

/// Support [`Vec`] for `std`/`alloc`.
#[cfg(feature = "alloc")]
impl GptHelper<Vec<Partition>> for Vec<Partition> {
    fn new() -> Vec<Partition> {
        // TODO: Const
        Vec::with_capacity(128)
    }

    fn as_slice(&self) -> &[Partition] {
        self.as_slice()
    }

    fn as_mut_slice(&mut self) -> &mut [Partition] {
        self.as_mut_slice()
    }

    fn push(&mut self, part: Partition) -> Result<()> {
        self.push(part);
        Ok(())
    }

    fn remove(&mut self, index: usize) -> Partition {
        self.remove(index)
    }
}

/// GUID Partition Table
///
/// All modifications are done in-memory,
/// and *should* only affect partition entries, not data anywhere else on disk.
///
/// Changes can be committed to disk with
/// [`GptC::to_bytes`]/[`GptC::to_writer`].
///
/// This type is largely agnostic to the underlying disk and block sizes.
/// It will remember the disk/block size it was created with, for convenience,
/// but these values may be changed if needed, for example when moving to a
/// differently sized disk.
///
/// Partitions are sorted by their starting offset in the partition array.
///
/// If you have strict `no_std` memory requirements,
/// this struct can be made smaller by limiting the number of
/// partitions it stores. No guarantees are made about the size of this struct.
///
/// Note that doing so will effectively "cut off" any partitions beyond that
/// value, if writing the GPT back out.
///
/// If possible you may instead want to use the `alloc` feature,
/// which allows usage of the smaller [`Vec`] rather than the inline
/// [`ArrayVec`].
///
/// # Examples
///
/// [`GptC`] supporting only 4 partitions.
///
/// ```rust
/// use parts::{arrayvec::ArrayVec, GptC, Partition, uuid::Uuid, types::*};
///
/// let gpt: GptC<ArrayVec<[Partition; 4]>> = GptC::new(
///     Uuid::nil(),
///     Size::from_mib(10),
///     BlockSize::new(512)
/// );
/// ```
#[derive(Copy, Debug, Clone, PartialEq)]
pub struct GptC<C> {
    uuid: Uuid,
    partitions: C,
    disk_size: Size,
    block_size: BlockSize,
}

/// See [`GptC`] for docs.
#[cfg(not(feature = "alloc"))]
pub type Gpt<C = ArrayVec<[Partition; 128]>> = GptC<C>;

/// See [`GptC`] for docs.
#[cfg(feature = "alloc")]
pub type Gpt<C = Vec<Partition>> = GptC<C>;

// Public APIs
impl<C: GptHelper<C>> Gpt<C> {
    /// New empty Gpt
    ///
    /// `uuid` must be unique, such as from [`Uuid::new_v4`].
    ///
    /// # Panics
    ///
    /// - If `disk_size` is zero.
    pub fn new(uuid: Uuid, disk_size: Size, block_size: BlockSize) -> Self {
        assert_ne!(disk_size.as_bytes(), 0, "Disk size must not be zero");
        Self {
            uuid,
            partitions: C::new(),
            disk_size,
            block_size,
        }
    }

    /// Read the Gpt from `source`
    ///
    /// # Errors
    ///
    /// - [`Error::Invalid`] if the GPT is invalid
    /// - [`Error::NotEnough`] if `source` is too small.
    pub fn from_bytes(source: &[u8], block_size: BlockSize) -> Result<Self> {
        GptC::from_bytes_with_func(
            |i, buf| {
                let i = i.0 as usize;
                let size = buf.len();
                buf.copy_from_slice(
                    source
                        .get(i..)
                        .ok_or(Error::NotEnough)?
                        .get(..size)
                        .ok_or(Error::NotEnough)?,
                );
                Ok(())
            },
            block_size,
            Size::from_bytes(source.len().try_into().expect("Source too large for u64")),
        )
    }

    /// Read the Gpt using `func`.
    ///
    /// `primary` must contain LBA0 and LBA1, for a length of `block_size * 2`
    /// bytes.
    ///
    /// `alt` must contain the last LBA, for a length of `block_size` bytes.
    ///
    /// `func` receives a byte offset into the device,
    /// and a buffer to read into.
    ///
    /// # Errors
    ///
    /// - [`Error::Invalid`] if the GPT is invalid
    /// - [`Error::NotEnough`] if `source`/`primary`/`alt` is too small.
    /// - If `func` does.
    ///
    /// # Examples
    ///
    /// Reads from a single byte slice.
    ///
    /// This example is better served by [`GptC::from_bytes`],
    /// but this method is useful when you don't have a single byte slice,
    /// as you can read from whatever you want to `buf`
    ///
    /// ```rust,no_run
    /// # use parts::{Gpt, Error, types::{BlockSize, Size}};
    /// # fn main() -> anyhow::Result<()> {
    /// # let source = &[];
    /// let gpt: Gpt = Gpt::from_bytes_with_func(
    ///     |offset, buf| {
    ///         let offset = offset.0 as usize;
    ///         let len = buf.len();
    ///         let data = source.get(offset..)
    ///             .ok_or(Error::NotEnough)?
    ///             .get(..len)
    ///             .ok_or(Error::NotEnough)?;
    ///         buf.copy_from_slice(data);
    ///         Ok(())
    ///     },
    ///     BlockSize::new(512),
    ///     Size::from_mib(10)
    /// ).unwrap();
    /// # Ok(()) }
    /// ```
    pub fn from_bytes_with_func<F: FnMut(Offset, &mut [u8]) -> Result<()>>(
        mut func: F,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Result<Self> {
        let _mbr = {
            let mut buf = [0; MBR_SIZE];
            func(Offset(0), &mut buf)?;
            ProtectiveMbr::from_bytes(&buf)?
        };
        let primary = {
            // NOTE: `block_size - 92` is reserved and must be zero, but we don't check.
            // FIXME: CRC is over header_size, which may be larger.
            let mut buf = [0; 92];
            func(Offset(block_size.get()), &mut buf)?;
            Header::from_bytes(&buf, block_size)?
        };
        let alt = {
            // NOTE: `block_size - 92` is reserved and must be zero, but we don't check.
            // FIXME: CRC is over header_size, which may be larger.
            let mut buf = [0; 92];
            let last: Block = (disk_size / block_size) - 1;
            func(last * block_size, &mut buf)?;
            Header::from_bytes(&buf, block_size)?
        };
        //
        let mut partitions = C::new();
        validate(
            &primary,
            &alt,
            &mut func,
            block_size,
            disk_size,
            |_, source| {
                let part = Partition::from_bytes(source)?;
                if part != Partition::new() {
                    let _ = partitions.push(part);
                }
                Ok(())
            },
        )?;

        Ok(GptC {
            uuid: primary.uuid,
            partitions,
            disk_size,
            block_size,
        })
    }

    /// Read the Gpt from `source`
    ///
    /// See [`GptC::from_bytes`] for more details.
    ///
    /// # Errors
    ///
    /// - [`Error::Invalid`] if the GPT is invalid
    /// - [`Error::NotEnough`] if `source` is too small.
    /// - [`Error::Io`] if I/O does.
    #[cfg(feature = "std")]
    pub fn from_reader<RS: Read + Seek>(mut source: RS, block_size: BlockSize) -> Result<Self> {
        let disk_size = Size::from_bytes(source.seek(SeekFrom::End(0))?);
        let gpt = GptC::from_bytes_with_func(
            |i, buf| {
                source.seek(SeekFrom::Start(i.0))?;
                source.read_exact(buf)?;
                Ok(())
            },
            block_size,
            disk_size,
        )?;
        Ok(gpt)
    }

    /// Write the Gpt to `dest`.
    ///
    /// # Errors
    ///
    /// - [`Error::NotEnough`] if `dest` is too small.
    /// - If all partitions do not fit within the usable blocks.
    ///
    /// # Details
    ///
    /// The Gpt will be written in the following order
    ///
    /// - The Protective MBR
    /// - The backup header
    /// - The backup partition array
    /// - The primary header
    /// - The primary partition array
    pub fn to_bytes(&self, dest: &mut [u8]) -> Result<()> {
        let size = Size::from_bytes(dest.len().try_into().unwrap());
        self.to_bytes_with_func(
            |i, buf| {
                let i = i.0 as usize;
                dest.get_mut(i..)
                    .ok_or(Error::NotEnough)?
                    .get_mut(..buf.len())
                    .ok_or(Error::NotEnough)?
                    .copy_from_slice(buf);
                Ok(())
            },
            self.block_size,
            size,
        )
    }

    /// Write the Gpt using `func`.
    ///
    /// `func` receives a byte offset, and a buffer to read from.
    /// It is your responsibility to write the buffer to the device.
    ///
    /// See [`GptC::to_bytes`] for more details.
    ///
    /// # Errors
    ///
    /// - If `func` does.
    /// - If all partitions do not fit within the usable blocks.
    ///
    /// # Examples
    pub fn to_bytes_with_func<F: FnMut(Offset, &[u8]) -> Result<()>>(
        &self,
        mut func: F,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Result<()> {
        let last_lba = (disk_size / block_size) - 1;
        {
            let mbr = ProtectiveMbr::new(last_lba);
            let mut mbr_buf = [0; MBR_SIZE];
            mbr.to_bytes(&mut mbr_buf)?;
            func(Size::from_bytes(0).into(), &mbr_buf)?;
        }

        let partition_len = self
            .partitions
            .as_slice()
            .len()
            .try_into()
            .expect("Too many partitions, would overflow u32");
        let mut partition_buf = [0; PARTITION_ENTRY_SIZE as usize];
        let mut digest = crc32::Digest::new(crc32::IEEE);
        for part in self.partitions.as_slice() {
            part.to_bytes(&mut partition_buf)?;
            digest.write(&partition_buf);
        }
        let parts_crc = digest.sum32();
        let disk_uuid = self.uuid;

        let alt = Header::new(
            HeaderKind::Backup,
            partition_len,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        // Verify all partitions are within bounds
        for part in self.partitions() {
            let a = part.start();
            let b = part.end();
            if (a < alt.first_usable) || (b > alt.last_usable) {
                return Err(Error::NotEnough);
            }
        }

        self.write_header_array(&mut func, alt, last_lba, block_size)?;

        let primary = Header::new(
            HeaderKind::Primary,
            partition_len,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        self.write_header_array(func, primary, Block(1), block_size)?;
        Ok(())
    }

    /// Write the Gpt to `dest`
    ///
    /// # Errors
    ///
    /// - If all partitions do not fit within the usable blocks.
    /// - [`Error::NotEnough`] if `dest` is too small.
    /// - [`Error::Io`] if I/O does.
    #[cfg(feature = "std")]
    pub fn to_writer<WS: Write + Seek>(&self, mut dest: WS) -> Result<()> {
        let disk_size = Size::from_bytes(dest.seek(SeekFrom::End(0))?);
        dest.seek(SeekFrom::Start(0))?;
        self.to_bytes_with_func(
            |i, buf| {
                dest.seek(SeekFrom::Start(i.0))?;
                dest.write_all(buf)?;
                Ok(())
            },
            self.block_size,
            disk_size,
        )?;
        Ok(())
    }

    /// Unique Disk UUID
    pub fn uuid(&self) -> Uuid {
        self.uuid
    }

    /// Slice of in-use partitions. Sorted by starting offset.
    pub fn partitions(&self) -> &[Partition] {
        self.partitions.as_slice()
    }

    /// Add a partition.
    ///
    /// # Errors
    ///
    /// - If `part` overlaps with existing partitions
    /// - In `no_std`, if `part` would overflow `C`.
    pub fn add_partition(&mut self, part: Partition) -> Result<()> {
        self.check_overlap(&part)?;
        self.partitions.push(part)?;
        self.partitions
            .as_mut_slice()
            .sort_unstable_by_key(|p| p.start());
        Ok(())
    }

    /// Remove the partition at `index`.
    pub fn remove_partition(&mut self, index: usize) -> Partition {
        self.partitions.remove(index)
    }

    /// Set the disk UUID.
    ///
    /// WARNING: Gpt UUID's MUST be unique.
    /// Only use this if you know what you're doing.
    pub fn set_uuid(&mut self, uuid: Uuid) {
        self.uuid = uuid;
    }

    /// The first usable partition [`Block`]
    pub fn first_usable(&self) -> Block {
        Header::usable(self.block_size, self.disk_size).0
    }

    /// The last usable partition [`Block`]
    pub fn last_usable(&self) -> Block {
        Header::usable(self.block_size, self.disk_size).1
    }

    /// The next usable block for a Partition
    ///
    /// Note that this is not aligned in any way.
    pub fn next_usable(&self) -> Block {
        self.partitions()
            .iter()
            // Plus 1 because `end` is inclusive
            .map(|p| p.end() + 1)
            .max()
            .unwrap_or_else(|| self.first_usable())
    }

    /// The next 1MiB aligned usable block for a Partition
    ///
    /// Rounds **up** from [`Gpt::next_usable`]
    pub fn next_usable_aligned(&self) -> Block {
        let next = self.next_usable();
        let block_1mib: Block = Size::from_mib(1) / self.block_size;
        let rem = next.0 % block_1mib.0;
        Block(next.0 + (block_1mib.0 - rem))
    }

    /// Remaining usable partition space
    pub fn remaining(&self) -> Size {
        // Plus 1 block because inclusive?
        (((self.last_usable() - self.next_usable().0) + 1) * self.block_size).into()
    }
}

// Private APIs
impl<C: GptHelper<C>> GptC<C> {
    fn check_overlap(&mut self, part: &Partition) -> Result<()> {
        for existing in self.partitions() {
            if part.start() >= existing.start() && part.start() <= existing.end() {
                return Err(Error::Overlap);
            }
        }
        Ok(())
    }

    fn write_header_array<F: FnMut(Offset, &[u8]) -> Result<()>>(
        &self,
        mut func: F,
        header: Header,
        last_lba: Block,
        block_size: BlockSize,
    ) -> Result<()> {
        let mut header_buf = [0; HEADER_SIZE as usize];
        let mut partition_buf = [0; PARTITION_ENTRY_SIZE as usize];
        //
        header.to_bytes(&mut header_buf)?;
        func(last_lba * block_size, &header_buf)?;
        for (i, part) in self.partitions.as_slice().iter().enumerate() {
            part.to_bytes(&mut partition_buf)?;
            let b =
                Offset((header.array * block_size).0 + ((PARTITION_ENTRY_SIZE as u64) * i as u64));
            func(b, &partition_buf)?;
        }
        //
        Ok(())
    }
}

/// Tests that should work without the std feature.
///
/// Still requires std exist, since test itself requires it.
#[cfg(test)]
mod test_no_std {
    use super::*;
    use crate::PartitionType;
    use core::mem;
    use pretty_assertions::assert_eq;
    use static_assertions::*;
    use uuid::Uuid;

    // FIXME: should be from crate::util
    // SAFETY: Not zero
    const BLOCK_SIZE: BlockSize = unsafe { BlockSize::new_unchecked(512) };
    type Result = super::Result<()>;

    type DefArray = ArrayVec<[Partition; 128]>;

    // Used by assert_eq_size
    #[allow(dead_code)]
    type EmptyArray = ArrayVec<[Partition; 0]>;

    // GptC is documented as being 32 bytes.
    assert_eq_size!(GptC<EmptyArray>, [u8; 32]);

    // Option<GptC> is documented as being 32 bytes.
    assert_eq_size!(Option<GptC<EmptyArray>>, [u8; 32]);

    //
    #[cfg(feature = "std")]
    assert_eq_size!(Gpt, [u8; 32 + mem::size_of::<Vec::<Partition>>()]);

    //
    #[cfg(not(feature = "std"))]
    assert_eq_size!(
        Gpt,
        [u8; 32 + mem::size_of::<ArrayVec::<[Partition; 128]>>()]
    );

    /// Should error when the MBR is invalid/missing.
    #[test]
    #[should_panic = "MBR signature invalid"]
    fn missing_mbr_test() {
        let raw = [0; (BLOCK_SIZE.get() * 2) as usize];
        let _gpt: Gpt = Gpt::from_bytes(&raw, BLOCK_SIZE).unwrap();
    }

    /// Prevent adding overlapping partitions
    #[test]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    fn invalid_partitions() {
        let mut gpt: Gpt = Gpt::new(Uuid::nil(), Size::from_mib(10), BLOCK_SIZE);
        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(gpt.first_usable())
            .end(gpt.first_usable() + 1)
            .partition_type(PartitionType::Unused);
        gpt.add_partition(part.finish()).unwrap();
        let e = gpt.add_partition(part.finish()).unwrap_err();
        panic!(e.to_string());
    }

    /// Partitions must be at least one block.
    #[test]
    #[should_panic(expected = "Invalid Partition Size")]
    fn invalid_partitions_size() {
        let mut gpt: Gpt = Gpt::new(Uuid::nil(), Size::from_mib(10), BLOCK_SIZE);
        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(Block(0))
            .size(Size::from_bytes(0))
            .partition_type(PartitionType::Unused);
        gpt.add_partition(part.finish()).unwrap();
    }

    /// A 512 byte partition should be valid
    #[test]
    fn valid_one_block_partition() {
        let mut gpt: Gpt = Gpt::new(Uuid::nil(), Size::from_mib(10), BLOCK_SIZE);
        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(gpt.first_usable())
            .end(gpt.first_usable())
            .partition_type(PartitionType::Unused);
        gpt.add_partition(part.finish()).unwrap();
    }

    /// Don't panic on slice indexing if given an empty slice,
    /// and don't allow an empty disk
    #[test]
    fn empty_regress() {
        let gpt = Gpt::<DefArray>::from_bytes(&[], BLOCK_SIZE);
        let e = gpt.unwrap_err();
        if let Error::NotEnough = e {
        } else {
            panic!("Wrong error");
        }
        //
        let gpt = Gpt::<DefArray>::from_bytes(&[], BLOCK_SIZE);
        let e = gpt.unwrap_err();
        if let Error::NotEnough = e {
        } else {
            panic!("Empty disk was allowed");
        }
    }

    /// Test that GptC::next_usable{_aligned} are correct
    #[test]
    fn next_usable() {
        let size = Size::from_mib(10);
        let mut gpt: Gpt = Gpt::new(Uuid::nil(), size, BLOCK_SIZE);
        assert_eq!(gpt.next_usable(), gpt.first_usable());
        assert_eq!(gpt.next_usable(), Block(34));
        assert_eq!(gpt.next_usable_aligned(), Block(2048));

        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(gpt.first_usable())
            .end(gpt.first_usable())
            .finish();
        gpt.add_partition(part).unwrap();
        assert_eq!(gpt.next_usable(), Block(35));

        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(gpt.next_usable_aligned())
            .end(gpt.next_usable_aligned())
            .finish();
        gpt.add_partition(part).unwrap();
        assert_eq!(gpt.next_usable(), Block(2049));
        assert_eq!(gpt.next_usable_aligned(), Block(4096));
    }

    /// Test GptC::remaining is correct
    // FIXME: Not confident this test/math is correct
    #[test]
    fn remaining() -> Result {
        let size = Size::from_mib(10);
        let mut gpt: Gpt = Gpt::new(Uuid::nil(), size, BLOCK_SIZE);
        let rem = gpt.remaining();
        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(gpt.first_usable())
            .size(rem)
            .finish();
        assert_eq!(
            part.end(),
            gpt.last_usable(),
            "Partition didn't use all available space"
        );
        // 10 MiB, minus 2 16 KiB partition arrays, minus 2 logical blocks
        // for the headers, minus 1 block for the MBR
        //
        // This should be exactly how much total usable partition space is
        // available.
        let expected: Size = size
            - (Size::from_kib(16) * 2)
            - (Size::from_bytes(BLOCK_SIZE.get()) * 2)
            - Size::from_bytes(BLOCK_SIZE.get());
        dbg!(expected, expected.as_mib());
        assert_eq!(rem, expected, "Remaining wasn't expected size");
        //
        let part = PartitionBuilder::new(Uuid::nil(), &gpt)
            .start(gpt.first_usable())
            // Minus 1 MiB, should leave exactly that much space left.
            .size(rem - Size::from_mib(1))
            .finish();
        gpt.add_partition(part)?;
        let rem = gpt.remaining();
        dbg!(rem);
        dbg!(rem.as_mib());
        assert_eq!(rem, Size::from_mib(1));
        Ok(())
    }

    /// Test that a newly created Gpt has no partitions
    #[test]
    fn empty_partitions() -> Result {
        let mut data = vec![0; 1024 * 1024];
        let gpt: Gpt = Gpt::new(Uuid::nil(), Size::from_mib(10), BLOCK_SIZE);
        gpt.to_bytes(&mut data)?;
        let gpt: Gpt = Gpt::from_bytes(&data, BLOCK_SIZE)?;
        assert_eq!(gpt.partitions().len(), 0);
        //
        Ok(())
    }
}

#[cfg(all(test, feature = "std"))]
mod test {
    use super::*;
    use crate::{
        partitions::PartitionType,
        util::{Result, *},
    };
    use pretty_assertions::assert_eq;
    use std::{io, vec::Vec as StdVec};

    type Array<N = [Partition; 128]> = ArrayVec<N>;
    type Vec = StdVec<Partition>;

    fn read_gpt_size<N>(raw: &[u8]) -> Result<Gpt<N>>
    where
        N: GptHelper<N> + core::fmt::Debug,
    {
        let gpt: Gpt<N> = Gpt::from_bytes_with_func(
            |i, buf| {
                let i = i.0 as usize;
                let size = buf.len();
                buf.copy_from_slice(&raw[i..][..size]);
                Ok(())
            },
            BLOCK_SIZE,
            Size::from_bytes(TEN_MIB_BYTES as u64),
        )
        .map_err(anyhow::Error::msg)?;
        //
        Ok(gpt)
    }

    /// Confirm the GPT has what we expect
    fn expected_gpt(gpt: Gpt) {
        assert_eq!(gpt.partitions().len(), 1);
        assert_eq!(
            gpt.partitions()[0].uuid(),
            Uuid::parse_str(CF_PART_GUID).unwrap()
        );
        assert_eq!(gpt.uuid, Uuid::parse_str(CF_DISK_GUID).unwrap());
    }

    /// Test that we can read a GPT from another tool
    #[test]
    fn read_gpt() -> Result {
        let raw = data()?;
        read_gpt_size::<Array<[Partition; 128]>>(&raw)?;
        read_gpt_size::<Array<[Partition; 0]>>(&raw)?;
        read_gpt_size::<Array<[Partition; 64]>>(&raw)?;
        read_gpt_size::<Array<[Partition; 256]>>(&raw)?;
        let _: Gpt = Gpt::from_bytes(&raw, BLOCK_SIZE)?;
        //
        let gpt = read_gpt_size::<Vec>(&raw)?;
        expected_gpt(gpt);
        //
        Ok(())
    }

    #[test]
    fn gpt_roundtrip() -> Result {
        let mut dest = vec![0; TEN_MIB_BYTES];
        let gpt = read_gpt_size::<Vec>(&data()?)?;
        gpt.to_bytes(&mut dest).map_err(anyhow::Error::msg)?;
        let new_gpt = read_gpt_size::<Vec>(&dest)?;
        assert_eq!(new_gpt, gpt);
        //
        gpt.to_bytes(&mut dest)?;
        let new_gpt = read_gpt_size::<Vec>(&dest)?;
        assert_eq!(new_gpt, gpt);
        Ok(())
    }

    #[test]
    #[should_panic = "Invalid Signature"]
    fn missing_gpt_test() {
        let mut raw = data().unwrap();
        raw[512..][..512].copy_from_slice(&[0; 512]);
        let _gpt = read_gpt_size::<Vec>(&raw).unwrap();
    }

    /// Test that the from_reader/to_writer methods work correctly
    #[test]
    fn reader_writer() -> Result {
        let raw = data()?;
        let mut raw = std::io::Cursor::new(raw);
        let gpt = Gpt::from_reader(&mut raw, BLOCK_SIZE)?;
        expected_gpt(gpt.clone());
        //
        raw.seek(SeekFrom::Start(0))?;
        raw.write_all(&b"\0".repeat(TEN_MIB_BYTES))?;
        gpt.to_writer(&mut raw)?;
        let gpt = Gpt::from_reader(&mut raw, BLOCK_SIZE)?;
        expected_gpt(gpt);
        //
        Ok(())
    }

    /// Make sure that writing out a GptC<ArrayVec<[Partition; N]>> is valid
    #[test]
    fn other_n_partitions() -> Result {
        let mut raw = data()?;
        let zero_gpt = read_gpt_size::<Array<[Partition; 0]>>(&raw)?;
        zero_gpt.to_bytes(&mut raw).map_err(anyhow::Error::msg)?;
        let gpt = read_gpt_size::<Vec>(&raw)?;
        assert_eq!(gpt.partitions().len(), 0);
        //
        Ok(())
    }

    /// Test that add_partition actually works
    ///
    /// Was first implemented using `partitions_mut` so index would
    /// always be out of bounds.
    #[test]
    fn add_partition_regress() -> Result {
        let raw = data()?;
        let mut gpt = read_gpt_size::<Vec>(&raw)?;
        let part = gpt.partitions()[0];
        // Just test that it doesn't panic
        let _ = gpt.add_partition(part);
        Ok(())
    }

    /// Prevent adding invalid partitions, outside the usable lba range.
    #[test]
    #[ignore]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    // TODO: invalid_range_partitions
    fn invalid_range_partitions() {
        // let raw = data().unwrap();
        // let mut gpt = read_gpt_size::<Vec>(&raw).unwrap();
        // let part = PartitionBuilder::new(Uuid::new_v4())
        //     .start(Size::from_mib(1).into())
        //     .size(Size::from_mib(1))
        //     .finish(BLOCK_SIZE);
        // let e = gpt.add_partition(part).unwrap_err();
        // panic!(e.to_string());
    }

    /// Create a GPT label more-or-less identical to our test data
    #[test]
    fn create_test_parts() -> Result {
        let test_data = data()?;
        let test_gpt = read_gpt_size::<Vec>(&test_data)?;
        //
        let mut gpt: Gpt<Vec> = Gpt::new(
            Uuid::parse_str(CF_DISK_GUID)?,
            Size::from_mib(10),
            BLOCK_SIZE,
        );
        let part = PartitionBuilder::new(Uuid::parse_str(CF_PART_GUID)?, &gpt)
            // FIXME: Shouldn't have to use BLOCK_SIZE here
            .start(Size::from_mib(1) / BLOCK_SIZE)
            .size(Size::from_mib(8))
            .partition_type(PartitionType::LinuxFilesystemData);
        gpt.add_partition(part.finish())?;
        assert_eq!(gpt, test_gpt);
        Ok(())
    }

    /// Test that a newly created Gpt has no partitions
    ///
    /// This *actually* tests that from_reader works
    #[test]
    fn empty_partitions_std() -> Result {
        let data = vec![0; TEN_MIB_BYTES];
        let mut data = io::Cursor::new(data);
        let gpt: Gpt = Gpt::new(Uuid::new_v4(), Size::from_mib(10), BLOCK_SIZE);
        gpt.to_writer(&mut data)?;
        let gpt: Gpt = Gpt::from_reader(&mut data, BLOCK_SIZE)?;
        assert_eq!(gpt.partitions().len(), 0);
        //
        Ok(())
    }
}
