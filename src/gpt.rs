//! Raw Gpt stuff
use self::{error::*, header::*, partition::*};
use crate::{
    mbr::{ProtectiveMbr, MBR_SIZE},
    types::*,
};
use arrayvec::{Array, ArrayVec};
use core::{convert::TryInto, mem};
use crc::{crc32, Hasher32};
#[cfg(feature = "std")]
use std::io::{prelude::*, SeekFrom};
use uuid::Uuid;

pub mod error;
mod header;
pub mod partition;

fn validate<F: FnMut(Offset, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8])>(
    primary: &Header,
    alt: &Header,
    mut func: F,
    block_size: BlockSize,
    disk_size: Size,
    mut cb: CB,
) -> Result<()> {
    if primary.this != Block::new(1, block_size) {
        return Err(Error::Invalid("Corrupt Primary GPT Header"));
    }
    let crc = calculate_part_crc(
        &mut func,
        primary.partitions as u64,
        primary.array.into_offset(),
        &mut cb,
    )?;
    if crc != primary.partitions_crc32 {
        return Err(Error::Invalid("Primary Partition Array CRC32 mismatch"));
    }
    let last_lba = (disk_size / block_size) - 1;
    if primary.alt != last_lba {
        return Err(Error::Invalid("Corrupt Primary GPT Header"));
    }
    //
    if alt.this != last_lba {
        return Err(Error::Invalid("Corrupt Backup GPT Header"));
    }
    if alt.alt != Block::new(1, block_size) {
        return Err(Error::Invalid("Corrupt Backup GPT Header"));
    }
    let crc = calculate_part_crc(
        &mut func,
        alt.partitions as u64,
        alt.array.into_offset(),
        &mut cb,
    )?;
    if crc != alt.partitions_crc32 {
        return Err(Error::Invalid("Backup Partition Array CRC32 mismatch"));
    }
    //
    Ok(())
}

pub trait GptHelper<C> {
    const SIZE: usize;

    fn new() -> C;

    fn as_slice(&self) -> &[Partition];

    fn as_mut_slice(&mut self) -> &mut [Partition];

    fn push(&mut self, part: Partition) -> Result<()>;

    fn remove(&mut self, index: usize) -> Partition;
}

impl<N: Array<Item = Partition>> GptHelper<ArrayVec<N>> for ArrayVec<N> {
    const SIZE: usize = mem::size_of::<ArrayVec<N>>();

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
        self.try_push(part).map_err(|_| Error::Overlap)
    }

    fn remove(&mut self, index: usize) -> Partition {
        self.remove(index)
    }
}

#[cfg(feature = "std")]
impl GptHelper<Vec<Partition>> for Vec<Partition> {
    const SIZE: usize = mem::size_of::<Vec<Partition>>();

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

/// Represents a GUID Partition Table
///
/// Note that all modifications are done in-memory
/// and *only* effect partition entries, not the data in them.
///
/// # Memory
///
/// When using `std`, partitions are by default stored in a `Vec`,
/// and there is no limit to how many can be read/written.
///
/// But when `no_std`, partitions are stored in an `ArrayVec`,
/// and will by default use at least `16KiB`, plus a variable amount depending
/// on `C`, of space.
///
/// This is because the GPT spec requires a minimum of 16KiB reserved
/// for the partition array.
///
/// If you are particularly memory-constrained, or need to support more
/// partitions, this type is generic over the container.
///
/// WARNING: Partitions can be effectively lost this way, during writing.
/// If there are 5 partitions and you constrain `GptC` to support only 4,
/// it's only possible to write the 4 back out,
/// the 5th will not be included in the partition CRC or array.
///
/// # Examples
///
/// `GptC` supporting only 4 partitions.
///
/// ```rust
/// # use parts::{arrayvec::ArrayVec, GptC, Partition, uuid::Uuid};
/// let gpt: GptC<ArrayVec<[Partition; 4]>> = GptC::new(Uuid::new_v4());
/// ```
#[derive(Debug, PartialEq)]
pub struct GptC<C> {
    uuid: Uuid,
    partitions: C,
}

/// See [`GptC`] for docs.
#[cfg(not(feature = "std"))]
pub type Gpt<C = ArrayVec<[Partition; 128]>> = GptC<C>;

/// See [`GptC`] for docs.
#[cfg(feature = "std")]
pub type Gpt<C = std::vec::Vec<Partition>> = GptC<C>;

// Public APIs
impl<C: GptHelper<C>> Gpt<C> {
    /// New empty Gpt
    ///
    /// WARNING: `uuid` must be unique, such as from [`Uuid::new_v4`].
    pub fn new(uuid: Uuid) -> Self {
        Self {
            uuid,
            partitions: C::new(),
        }
    }

    /// Read the Gpt from `source`
    ///
    /// # Errors
    ///
    /// - If the GPT is invalid
    /// - If `source` is not `disk_size`
    pub fn from_bytes(source: &[u8], block_size: BlockSize, disk_size: Size) -> Result<Self> {
        assert_eq!(
            source.len(),
            disk_size.as_bytes().try_into().unwrap(),
            "Invalid source"
        );
        let b_size = block_size.0 as usize;
        let d_size = disk_size.as_bytes() as usize;
        let primary = &source[..b_size * 2];
        let alt = &source[d_size - b_size..];
        GptC::from_bytes_with_func(
            primary,
            alt,
            |i, buf| {
                let i = i.0 as usize;
                let size = buf.len();
                buf.copy_from_slice(&source[i..][..size]);
                Ok(())
            },
            block_size,
            disk_size,
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
    /// See [`Gpt::from_bytes`] for more details.
    ///
    /// # Errors
    ///
    /// - If `func` does.
    ///
    /// # Examples
    pub fn from_bytes_with_func<F: FnMut(Offset, &mut [u8]) -> Result<()>>(
        primary: &[u8],
        alt: &[u8],
        mut func: F,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Result<Self> {
        let b_size = block_size.0 as usize;
        assert_eq!(primary.len(), b_size * 2, "Invalid primary");
        assert_eq!(alt.len(), b_size, "Invalid alt");
        let _mbr = ProtectiveMbr::from_bytes(&primary[..MBR_SIZE])
            .map_err(|_| Error::Invalid("Invalid Protective MBR"))?;
        let primary = Header::from_bytes(&primary[MBR_SIZE..], block_size)?;
        let alt = Header::from_bytes(alt, block_size)?;
        //
        let mut partitions = C::new();
        validate(
            &primary,
            &alt,
            &mut func,
            block_size,
            disk_size,
            |_, source| {
                let _ = partitions.push(Partition::from_bytes(source, block_size));
            },
        )?;

        Ok(GptC {
            uuid: primary.uuid,
            partitions,
        })
    }

    /// Read the Gpt from `source`
    ///
    /// See [`Gpt::from_bytes`] for more details.
    ///
    /// # Errors
    ///
    /// - If I/O does.
    #[cfg(feature = "std")]
    pub fn from_reader<RS: Read + Seek>(
        mut source: RS,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Result<Self> {
        let last_lba = (disk_size / block_size) - 1;
        let mut primary = vec![0; (block_size.0 * 2) as usize];
        let mut alt = vec![0; block_size.0 as usize];
        source.seek(SeekFrom::Start(0))?;
        source.read_exact(&mut primary)?;
        source.seek(SeekFrom::Start(last_lba.into_offset().0))?;
        source.read_exact(&mut alt)?;
        let gpt = GptC::from_bytes_with_func(
            &primary,
            &alt,
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
    /// - If all partitions do not fit within the usable blocks
    ///
    /// # Panics
    ///
    /// - If dest is not `disk_size`
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
    pub fn to_bytes(&self, dest: &mut [u8], block_size: BlockSize, disk_size: Size) -> Result<()> {
        assert_eq!(
            dest.len(),
            disk_size.as_bytes().try_into().unwrap(),
            "Invalid dest"
        );
        self.to_bytes_with_func(
            |i, buf| {
                let i = i.0 as usize;
                dest[i..][..buf.len()].copy_from_slice(buf);
                Ok(())
            },
            block_size,
            disk_size,
        )
    }

    /// Write the Gpt using `func`.
    ///
    /// `func` receives a byte offset into the device,
    /// and a buffer to write to the device.
    ///
    /// See [`Gpt::to_bytes`] for more details.
    ///
    /// # Errors
    ///
    /// - If `func` does.
    ///
    /// # Examples
    pub fn to_bytes_with_func<F: FnMut(Offset, &[u8]) -> Result<()>>(
        &self,
        mut func: F,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Result<()> {
        let last_lba = (disk_size / block_size) - 1;
        let mbr = ProtectiveMbr::new(last_lba);
        let mut mbr_buf = [0; MBR_SIZE];
        mbr.to_bytes(&mut mbr_buf);
        func(Size::from_bytes(0).into(), &mbr_buf)?;
        //
        let partition_len = self.partitions.as_slice().len().try_into().unwrap();
        let mut partition_buf = [0; PARTITION_ENTRY_SIZE as usize];
        let mut digest = crc32::Digest::new(crc32::IEEE);
        // FIXME: Invalid for N lower than 128?
        for part in self.partitions.as_slice() {
            part.to_bytes(&mut partition_buf, block_size);
            digest.write(&partition_buf);
        }
        let parts_crc = digest.sum32();
        let disk_uuid = self.uuid;

        let alt = Header::new(
            last_lba,
            Block::new(1, block_size),
            partition_len,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        // Verify all partitions are within bounds
        for part in self.partitions() {
            let a = part.start() / block_size;
            let b = part.end() / block_size;
            if (a < alt.first_usable) || (b > alt.last_usable) {
                return Err(Error::NotEnough);
            }
        }
        //
        self.write_header_array(&mut func, alt, last_lba, block_size)?;
        //
        let primary = Header::new(
            Block::new(1, block_size),
            last_lba,
            partition_len,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        self.write_header_array(func, primary, Block::new(1, block_size), block_size)?;
        Ok(())
    }

    /// Write the Gpt to `dest`
    ///
    /// See [`Gpt::to_bytes`] for more details.
    ///
    /// # Errors
    ///
    /// - If I/O does.
    #[cfg(feature = "std")]
    pub fn to_writer<WS: Write + Seek>(
        &self,
        mut dest: WS,
        block_size: BlockSize,
        disk_size: Size,
    ) -> Result<()> {
        self.to_bytes_with_func(
            |i, buf| {
                dest.seek(SeekFrom::Start(i.0))?;
                dest.write_all(buf)?;
                Ok(())
            },
            block_size,
            disk_size,
        )?;
        Ok(())
    }

    /// Unique Disk UUID
    pub fn uuid(&self) -> Uuid {
        self.uuid
    }

    /// Slice of in-use partitions
    pub fn partitions(&self) -> &[Partition] {
        self.partitions.as_slice()
    }

    /// Mutable slice of in-use partitions.
    pub fn partitions_mut(&mut self) -> &mut [Partition] {
        self.partitions.as_mut_slice()
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
        self.partitions_mut().sort_unstable_by_key(|p| p.start());
        Ok(())
    }

    /// Remove the partition at `index`.
    // FIXME: Where is the index supposed to come from, exactly?
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

    // TODO: First/last usable block getters, and remaining. Store disk/block size?
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
        header.to_bytes(&mut header_buf);
        func(last_lba.into_offset(), &header_buf)?;
        for (i, part) in self.partitions.as_slice().iter().enumerate() {
            part.to_bytes(&mut partition_buf, block_size);
            let b =
                Offset(header.array.into_offset().0 + ((PARTITION_ENTRY_SIZE as u64) * i as u64));
            func(b, &partition_buf)?;
        }
        //
        Ok(())
    }
}

/// Tests that should work without std
#[cfg(test)]
mod test_new_no_std {
    use super::*;
    use crate::PartitionType;
    use core::mem;
    use static_assertions::*;
    use uuid::Uuid;

    #[cfg(feature = "std")]
    assert_eq_size!(Gpt, [u8; mem::size_of::<Uuid>() + Vec::<Partition>::SIZE]);

    #[cfg(not(feature = "std"))]
    assert_eq_size!(
        Gpt,
        [u8; mem::size_of::<Uuid>() + ArrayVec::<[Partition; 128]>::SIZE]
    );

    #[test]
    #[should_panic = "Invalid Protective MBR"]
    fn missing_mbr_test() {
        let raw = [0; 1024];
        let _gpt: Gpt = Gpt::from_bytes(&raw, BlockSize(512), Size::from_bytes(1024)).unwrap();
    }

    /// Prevent adding overlapping partitions
    #[test]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    fn invalid_partitions() {
        let block_size = BlockSize(512);
        let mut gpt: Gpt = Gpt::new(Uuid::nil());
        let part = PartitionBuilder::new(Uuid::nil())
            .start(Offset(0))
            .end(Offset(512))
            .partition_type(PartitionType::Unused);
        gpt.add_partition(part.finish(block_size)).unwrap();
        let e = gpt.add_partition(part.finish(block_size)).unwrap_err();
        panic!(e.to_string());
    }

    /// Partitions must be at least one block.
    #[test]
    #[should_panic(expected = "Invalid Partition Size")]
    fn invalid_partitions_size() {
        let block_size = BlockSize(512);
        let mut gpt: Gpt = Gpt::new(Uuid::nil());
        let part = PartitionBuilder::new(Uuid::nil())
            .start(Offset(0))
            .end(Offset(0))
            .partition_type(PartitionType::Unused);
        gpt.add_partition(part.finish(block_size)).unwrap();
    }
}

#[cfg(all(test, feature = "std"))]
mod test_new {
    use super::*;

    #[test]
    fn feature() {
        let gpt: Gpt = Gpt::new(Uuid::new_v4());
        dbg!(gpt);
        // panic!();
    }
}

#[cfg(any())]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        partitions::PartitionType,
        util::{Result, *},
    };
    use core::mem;
    use generic_array::{
        typenum::{Unsigned, U0, U128, U256, U64},
        ArrayLength,
    };
    use static_assertions::*;
    use std::io;

    assert_eq_size!(
        Gpt,
        [u8; MIN_PARTITIONS_BYTES as usize + mem::size_of::<[u8; 16]>() + mem::size_of::<u64>()]
    );

    fn read_gpt_size<N>(raw: &[u8]) -> Result<Gpt<N>>
    where
        N: Unsigned,
        N: ArrayLength<Partition>,
        N::ArrayType: Copy,
    {
        let block = BLOCK_SIZE.0 as usize;

        let primary = &raw[..block * 2];
        let alt = &raw[raw.len() - block..];
        let gpt: Gpt<N> = Gpt::from_bytes_with_size(
            &primary,
            &alt,
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
        let gpt = read_gpt_size::<U128>(&raw)?;
        read_gpt_size::<U0>(&raw)?;
        read_gpt_size::<U64>(&raw)?;
        read_gpt_size::<U256>(&raw)?;
        Gpt::from_bytes(&raw, BLOCK_SIZE, Size::from_bytes(TEN_MIB_BYTES as u64))?;
        //
        expected_gpt(gpt);
        //
        Ok(())
    }

    //
    #[test]
    fn gpt_roundtrip() -> Result {
        let mut dest = vec![0; TEN_MIB_BYTES];
        let gpt = read_gpt_size::<U128>(&data()?)?;
        gpt.to_bytes_with_size(
            |i, buf| {
                let i = i.0 as usize;
                dest[i..][..buf.len()].copy_from_slice(buf);
                Ok(())
            },
            BLOCK_SIZE,
            Size::from_bytes(TEN_MIB_BYTES as u64),
        )
        .map_err(anyhow::Error::msg)?;
        let new_gpt = read_gpt_size::<U128>(&dest)?;
        assert_eq!(new_gpt, gpt);
        //
        gpt.to_bytes(
            &mut dest,
            BLOCK_SIZE,
            Size::from_bytes(TEN_MIB_BYTES as u64),
        )?;
        let new_gpt = read_gpt_size::<U128>(&dest)?;
        assert_eq!(new_gpt, gpt);
        Ok(())
    }

    #[test]
    #[should_panic = "Invalid Signature"]
    fn missing_gpt_test() {
        let mut raw = data().unwrap();
        raw[512..][..512].copy_from_slice(&[0; 512]);
        let _gpt = read_gpt_size::<U128>(&raw).unwrap();
    }

    /// Test that the from_reader/to_writer methods work correctly
    #[test]
    #[cfg(feature = "std")]
    fn std_gpt_test() -> Result {
        let raw = data()?;
        let raw = std::io::Cursor::new(raw);
        let gpt = Gpt::from_reader(raw, BLOCK_SIZE, Size::from_bytes(TEN_MIB_BYTES as u64))?;
        expected_gpt(gpt);
        //
        Ok(())
    }

    /// Don't panic on slice indexing if given an empty slice
    #[test]
    // FIXME: from_bytes_with_size takes `primary` and `alt`,
    // and panics if they're not block_size.
    #[ignore]
    fn empty_bytes_regress() {
        let raw = &[];
        let gpt = Gpt::<U128>::from_bytes_with_size(
            raw,
            raw,
            |i, buf| {
                let i = i.0 as usize;
                let size = buf.len();
                buf.copy_from_slice(&raw[i..][..size]);
                Ok(())
            },
            BLOCK_SIZE,
            Size::from_bytes(TEN_MIB_BYTES as u64),
        );
        let e = gpt.unwrap_err();
        if let Error::NotEnough = e {
            panic!("Wrong error");
        }
    }

    /// Make sure that if a `Gpt<U0>` is written to a device with 1 partition,
    /// that the partition destroyed/ignored.
    /// Basically it should output a valid GPT Header
    #[test]
    fn destroy_unsupported_partitions() -> Result {
        let mut raw = data()?;
        let zero_gpt = read_gpt_size::<U0>(&raw)?;
        zero_gpt
            .to_bytes_with_size(
                |i, buf| {
                    let i = i.0 as usize;
                    raw[i..][..buf.len()].copy_from_slice(buf);
                    Ok(())
                },
                BLOCK_SIZE,
                Size::from_bytes(TEN_MIB_BYTES as u64),
            )
            .map_err(anyhow::Error::msg)?;
        let gpt = read_gpt_size::<U128>(&raw)?;
        assert_eq!(gpt.partitions().len(), 0);
        //
        Ok(())
    }

    /// Test that add_partition actually works
    ///
    /// Was first implemented using `partitions_mut` so index would
    /// always be out of bounds. Oops.
    #[test]
    fn add_partition_regress() -> Result {
        let raw = data()?;
        let mut gpt = read_gpt_size::<U128>(&raw)?;
        let part = gpt.partitions()[0];
        // Just test that it doesn't panic
        let _ = gpt.add_partition(part);
        Ok(())
    }

    /// Prevent adding invalid partitions, outside the usable lba range.
    #[test]
    #[ignore]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    fn invalid_range_partitions() {
        let raw = data().unwrap();
        let mut gpt = read_gpt_size::<U128>(&raw).unwrap();
        let part = PartitionBuilder::new(Uuid::new_v4())
            .start(Size::from_mib(1).into())
            .size(Size::from_mib(1))
            .finish(BLOCK_SIZE);
        let e = gpt.add_partition(part).unwrap_err();
        panic!(e.to_string());
    }

    /// Create a GPT label more-or-less identical to our test data
    #[test]
    fn create_test_parts() -> Result {
        let test_data = data()?;
        let test_gpt = read_gpt_size::<U128>(&test_data)?;
        //
        let mut gpt: Gpt<U128> = Gpt::new();
        gpt.set_uuid(Uuid::parse_str(CF_DISK_GUID)?);
        let part = PartitionBuilder::new(Uuid::parse_str(CF_PART_GUID)?)
            .start(Size::from_mib(1).into())
            .size(Size::from_mib(8))
            .partition_type(PartitionType::LinuxFilesystemData);
        gpt.add_partition(part.finish(BLOCK_SIZE))?;
        assert_eq!(gpt, test_gpt);
        Ok(())
    }

    /// Test that a newly created Gpt has no partitions
    #[test]
    fn empty_partitions() -> Result {
        let mut data = vec![0; TEN_MIB_BYTES];
        let size = Size::from_bytes(TEN_MIB_BYTES as u64);
        let gpt = Gpt::new();
        gpt.to_bytes(&mut data, BLOCK_SIZE, size)?;
        let gpt = Gpt::from_bytes(&data, BLOCK_SIZE, size)?;
        assert_eq!(gpt.partitions().len(), 0);
        //
        Ok(())
    }

    /// Test that a newly created Gpt has no partitions
    #[test]
    fn empty_partitions_std() -> Result {
        let data = vec![0; TEN_MIB_BYTES];
        let mut data = io::Cursor::new(data);
        let size = Size::from_bytes(TEN_MIB_BYTES as u64);
        let gpt = Gpt::new();
        gpt.to_writer(&mut data, BLOCK_SIZE, size)?;
        let gpt = Gpt::from_reader(&mut data, BLOCK_SIZE, size)?;
        assert_eq!(gpt.partitions().len(), 0);
        //
        Ok(())
    }
}
