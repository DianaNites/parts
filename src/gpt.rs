//! Raw Gpt stuff
use self::{error::*, header::*, partition::*};
use crate::{
    mbr::{ProtectiveMbr, MBR_SIZE},
    types::*,
};
use core::fmt;
use crc::{crc32, Hasher32};
use generic_array::{
    sequence::GenericSequence,
    typenum::{Unsigned, U128},
    ArrayLength,
    GenericArray,
};
#[cfg(feature = "std")]
use std::io::prelude::*;
#[cfg(feature = "std")]
use std::io::SeekFrom;
use uuid::Uuid;

pub mod error;
mod header;
pub mod partition;

fn validate<F: FnMut(ByteSize, &mut [u8]) -> Result<()>, CB: FnMut(usize, &[u8])>(
    primary: &Header,
    alt: &Header,
    mut func: F,
    block_size: BlockSize,
    disk_size: ByteSize,
    mut cb: CB,
) -> Result<()> {
    if primary.this != LogicalBlockAddress(1) {
        return Err(Error::Invalid("Corrupt Primary GPT Header"));
    }
    let crc = calculate_part_crc(
        &mut func,
        primary.partitions as u64,
        block_size,
        primary.array,
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
    if alt.alt != LogicalBlockAddress(1) {
        return Err(Error::Invalid("Corrupt Backup GPT Header"));
    }
    let crc = calculate_part_crc(
        &mut func,
        alt.partitions as u64,
        block_size,
        alt.array,
        &mut cb,
    )?;
    if crc != alt.partitions_crc32 {
        return Err(Error::Invalid("Backup Partition Array CRC32 mismatch"));
    }
    //
    Ok(())
}

/// Represents a GUID Partition Table
///
/// Note that all modifications are done in-memory
/// and *only* effect partition entries, not the data in them.
///
/// # Memory
///
/// By default this takes `16KiB + 24 bytes` of space.
/// The UEFI spec requires a minimum of 16KiB reserved for partitions,
/// which is 128 partitions if each entry is 128 bytes,
/// which we assume by default.
///
/// If you are particularly space-constrained, or need to support more,
/// you can use [`crate::typenum`] to set the `N` generic parameter to
/// the number of partitions you want to support.
///
/// When doing this unsupported partitions will ***not*** be preserved,
/// and depending on `N`, and what you do, may be overwritten by
/// newly added partitions.
///
/// Regardless of `N`, when reading the full partition array *is* still
/// validated.
#[derive(Copy, Clone, PartialEq)]
pub struct Gpt<N = U128>
where
    N: ArrayLength<Partition> + Unsigned,
    N::ArrayType: Copy,
{
    uuid: Uuid,
    partitions: GenericArray<Partition, N>,
    /// Real size of the partitions array.
    /// u64, not u32, for alignment reasons.
    partitions_len: u64,
}

impl Gpt {
    /// Read the GPT from a byte slice
    ///
    /// See [`Gpt::from_bytes_with_size`] if getting a slice of
    /// the entire disk isn't possible.
    pub fn from_bytes(source: &[u8], block_size: BlockSize, disk_size: ByteSize) -> Result<Self> {
        let b_size = block_size.0 as usize;
        let d_size = disk_size.as_bytes() as usize;
        let primary = &source[..b_size * 2];
        let alt = &source[d_size - b_size..];
        Gpt::from_bytes_with_size(
            primary,
            alt,
            |i, buf| {
                let i = i.as_bytes() as usize;
                let size = buf.len();
                buf.copy_from_slice(&source[i..][..size]);
                Ok(())
            },
            block_size,
            disk_size,
        )
    }

    /// Write the full GPT to a byte slice
    ///
    /// See [`Gpt::to_bytes_with_size`] if getting a slice of
    /// the entire disk isn't possible,
    /// and for details of what gets written and in what order.
    pub fn to_bytes(
        &self,
        dest: &mut [u8],
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<()> {
        self.to_bytes_with_size(
            |i, buf| {
                let i = i.as_bytes() as usize;
                dest[i..][..buf.len()].copy_from_slice(buf);
                Ok(())
            },
            block_size,
            disk_size,
        )
    }
}

#[cfg(feature = "std")]
impl Gpt {
    /// Read the GPT from a [`Read`]er.
    ///
    /// See [`Gpt::from_bytes`] for more details.
    pub fn from_reader<RS: Read + Seek>(
        source: RS,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<Self> {
        Gpt::from_reader_with_size(source, block_size, disk_size)
    }

    /// Write the GPT to a [`Write`]r.
    ///
    /// See [`Gpt::to_bytes`] for more details.
    pub fn to_writer<WS: Write + Seek>(
        &self,
        dest: WS,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<()> {
        self.to_writer_with_size(dest, block_size, disk_size)
    }
}

impl<N> Gpt<N>
where
    N: ArrayLength<Partition> + Unsigned,
    N::ArrayType: Copy,
{
    /// Like [`Gpt::from_bytes`] but stores `N` partitions
    /// instead of the minimum reserved amount.
    ///
    /// You probably don't want this method, but it can be useful
    /// if you're fine with only supporting a few partitions.
    ///
    /// `primary` must contain LBA0 and LBA1. That is, `block_size * 2` bytes.
    ///
    /// `alt` must be the last LBA. That is, `block_size` bytes.
    ///
    /// `func` is called to read data. Errors are propagated.
    /// It's arguments are a byte offset and a buffer to read into.
    pub fn from_bytes_with_size<F: FnMut(ByteSize, &mut [u8]) -> Result<()>>(
        primary: &[u8],
        alt: &[u8],
        mut func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<Self> {
        let b_size = block_size.0 as usize;
        assert_eq!(primary.len(), b_size * 2, "Invalid primary");
        assert_eq!(alt.len(), b_size, "Invalid alt");
        let _mbr = ProtectiveMbr::from_bytes(&primary[..MBR_SIZE])
            .map_err(|_| Error::Invalid("Invalid Protective MBR"))?;
        let primary = Header::from_bytes(&primary[MBR_SIZE..], block_size)?;
        let alt = Header::from_bytes(alt, block_size)?;
        //
        let mut partitions = GenericArray::<Partition, N>::generate(|_| Partition::new());
        validate(
            &primary,
            &alt,
            &mut func,
            block_size,
            disk_size,
            |i, source| {
                if i < partitions.len() {
                    partitions[i] = Partition::from_bytes(source, block_size);
                }
            },
        )?;

        Ok(Gpt {
            uuid: primary.uuid,
            // Only count used partitions.
            partitions_len: partitions
                .iter()
                .filter(|p| **p != Partition::new())
                .count() as u64,
            partitions,
        })
    }

    /// Like [`Gpt::to_bytes`] but stores `N` partitions.
    ///
    /// `disk_size` must be the size of the device.
    ///
    /// `func` will be called to write data.
    ///
    /// As an argument it receives the byte offset to write at, and
    /// a buffer of data to write.
    ///
    /// It returns a `Result<()>`, and errors are propagated.
    ///
    /// # Errors
    ///
    /// If all partitions do not fit within the usable blocks
    ///
    /// # Details
    ///
    /// This will tell `func` to write, in order:
    ///
    /// - The Protective MBR
    /// - The backup header
    /// - The backup header array
    /// - The primary header
    /// - The primary header array
    pub fn to_bytes_with_size<F: FnMut(ByteSize, &[u8]) -> Result<()>>(
        &self,
        mut func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<()> {
        let last_lba = (disk_size / block_size) - 1;
        let mbr = ProtectiveMbr::new(last_lba);
        let mut mbr_buf = [0; MBR_SIZE];
        mbr.to_bytes(&mut mbr_buf);
        func(ByteSize::from_bytes(0), &mbr_buf)?;
        //
        let mut partition_buf = [0; PARTITION_ENTRY_SIZE as usize];
        let mut digest = crc32::Digest::new(crc32::IEEE);
        for part in self.partitions() {
            part.to_bytes(&mut partition_buf, block_size);
            digest.write(&partition_buf);
        }
        let parts_crc = digest.sum32();
        let disk_uuid = self.uuid;

        let alt = Header::new(
            last_lba,
            LogicalBlockAddress(1),
            self.partitions_len as u32,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        // Verify all partitions are within bounds
        for part in self.partitions() {
            if ((part.start() / block_size) < alt.first_usable)
                || ((part.end() / block_size) > alt.last_usable)
            {
                return Err(Error::NotEnough);
            }
        }
        //
        self.write_header_array(&mut func, alt, last_lba, block_size)?;
        //
        let primary = Header::new(
            LogicalBlockAddress(1),
            last_lba,
            self.partitions_len as u32,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        self.write_header_array(func, primary, LogicalBlockAddress(1), block_size)?;
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<N> Gpt<N>
where
    N: ArrayLength<Partition> + Unsigned,
    N::ArrayType: Copy,
{
    /// Create a new GPT Table with no partitions
    ///
    /// This requires the `std` feature to generate a unique Uuid.
    ///
    /// See [`Gpt::with_uuid`] for a `no_std` solution.
    // Gpt can't be `Default`, this is std only.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Gpt {
            uuid: Uuid::new_v4(),
            partitions: GenericArray::<Partition, N>::generate(|_| Partition::new()),
            partitions_len: 0,
        }
    }

    /// Like [`Gpt::from_bytes_with_size`] but for readers
    pub fn from_reader_with_size<RS: Read + Seek>(
        mut source: RS,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<Self> {
        let last_lba = (disk_size / block_size) - 1;
        let mut primary = vec![0; block_size.0 as usize * 2];
        let mut alt = vec![0; block_size.0 as usize];
        source.read_exact(&mut primary)?;
        source.seek(SeekFrom::Start((last_lba * block_size).as_bytes()))?;
        source.read_exact(&mut alt)?;
        let gpt = Gpt::from_bytes_with_size(
            &primary,
            &alt,
            |i, buf| {
                source.seek(SeekFrom::Start(i.as_bytes()))?;
                source.read_exact(buf)?;
                Ok(())
            },
            block_size,
            disk_size,
        )?;
        Ok(gpt)
    }

    /// Like [`Gpt::to_bytes_with_size`] but for writers
    pub fn to_writer_with_size<WS: Write + Seek>(
        &self,
        mut dest: WS,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<()> {
        self.to_bytes_with_size(
            |i, buf| {
                dest.seek(SeekFrom::Start(i.as_bytes()))?;
                dest.write_all(buf)?;
                Ok(())
            },
            block_size,
            disk_size,
        )?;
        Ok(())
    }
}

impl<N> Gpt<N>
where
    N: ArrayLength<Partition> + Unsigned,
    N::ArrayType: Copy,
{
    /// Create a new GPT Table
    ///
    /// See [`Gpt::new`] for details.
    // TODO: Take random data instead?
    // Don't want people using a duplicate Uuid from Gpt::uuid?
    // Plus need to create Uuid's for partitions? Problem for the Builder?
    pub fn with_uuid(uuid: Uuid) -> Self {
        Gpt {
            uuid,
            partitions: GenericArray::<Partition, N>::generate(|_| Partition::new()),
            partitions_len: 0,
        }
    }

    /// Disk UUID
    pub fn uuid(&self) -> Uuid {
        self.uuid
    }

    /// Slice of in-use partitions
    pub fn partitions(&self) -> &[Partition] {
        let len = core::cmp::min(self.partitions_len as usize, self.partitions.len());
        &self.partitions[..len]
    }

    /// Mutable slice of in-use partitions.
    pub fn partitions_mut(&mut self) -> &mut [Partition] {
        let len = core::cmp::min(self.partitions_len as usize, self.partitions.len());
        &mut self.partitions[..len]
    }

    /// Add a partition
    pub fn add_partition(&mut self, part: Partition) -> Result<()> {
        self.check_overlap(&part)?;
        let len = core::cmp::min(self.partitions_len as usize, self.partitions.len());
        self.partitions[len] = part;
        self.partitions_len += 1;
        self.partitions_mut().sort_unstable_by_key(|p| p.start());
        Ok(())
    }

    /// Remove the partition at `index`.
    // FIXME: Where is the index supposed to come from, exactly?
    pub fn remove_partition(&mut self, index: usize) {
        self.partitions_mut()[index] = Partition::new();
        self.partitions_len -= 1;
        self.partitions_mut().sort_unstable_by_key(|p| p.start());
    }

    // TODO: First/last usable block getters, and remaining. Store disk/block size?
}

// Private APIs
impl<N> Gpt<N>
where
    N: ArrayLength<Partition> + Unsigned,
    N::ArrayType: Copy,
{
    fn check_overlap(&mut self, part: &Partition) -> Result<()> {
        for existing in self.partitions() {
            if part.start() >= existing.start() && part.start() <= existing.end() {
                return Err(Error::Overlap);
            }
        }
        Ok(())
    }

    fn write_header_array<F: FnMut(ByteSize, &[u8]) -> Result<()>>(
        &self,
        mut func: F,
        header: Header,
        last_lba: LogicalBlockAddress,
        block_size: BlockSize,
    ) -> Result<()> {
        let mut header_buf = [0; HEADER_SIZE as usize];
        let mut partition_buf = [0; PARTITION_ENTRY_SIZE as usize];
        //
        header.to_bytes(&mut header_buf);
        func(last_lba * block_size, &header_buf)?;
        for (i, part) in self.partitions().iter().enumerate() {
            part.to_bytes(&mut partition_buf, block_size);
            let b = header.array * block_size;
            let b = b + (ByteSize::from_bytes(PARTITION_ENTRY_SIZE as u64) * i as u64);
            func(b, &partition_buf)?;
        }
        //
        Ok(())
    }
}

impl<N> fmt::Debug for Gpt<N>
where
    N: ArrayLength<Partition> + Unsigned,
    N::ArrayType: Copy,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Gpt")
            .field("uuid", &self.uuid)
            .field("partitions", &self.partitions())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use core::mem;
    use generic_array::{
        typenum::{Unsigned, U0, U128, U256, U64},
        ArrayLength,
    };
    use static_assertions::*;

    assert_eq_size!(RawPartition, [u8; PARTITION_ENTRY_SIZE as usize]);
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
                let i = i.as_bytes() as usize;
                let size = buf.len();
                buf.copy_from_slice(&raw[i..][..size]);
                Ok(())
            },
            BLOCK_SIZE,
            ByteSize::from_bytes(TEN_MIB_BYTES as u64),
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
        Gpt::from_bytes(&raw, BLOCK_SIZE, ByteSize::from_bytes(TEN_MIB_BYTES as u64))?;
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
                let i = i.as_bytes() as usize;
                dest[i..][..buf.len()].copy_from_slice(buf);
                Ok(())
            },
            BLOCK_SIZE,
            ByteSize::from_bytes(TEN_MIB_BYTES as u64),
        )
        .map_err(anyhow::Error::msg)?;
        let new_gpt = read_gpt_size::<U128>(&dest)?;
        assert_eq!(new_gpt, gpt);
        //
        gpt.to_bytes(
            &mut dest,
            BLOCK_SIZE,
            ByteSize::from_bytes(TEN_MIB_BYTES as u64),
        )?;
        let new_gpt = read_gpt_size::<U128>(&dest)?;
        assert_eq!(new_gpt, gpt);
        Ok(())
    }

    #[test]
    #[should_panic = "Invalid Protective MBR"]
    fn missing_mbr_test() {
        let raw = [0; 1024];
        let _gpt = read_gpt_size::<U128>(&raw).unwrap();
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
        let gpt = Gpt::from_reader(raw, BLOCK_SIZE, ByteSize::from_bytes(TEN_MIB_BYTES as u64))?;
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
                let i = i.as_bytes() as usize;
                let size = buf.len();
                buf.copy_from_slice(&raw[i..][..size]);
                Ok(())
            },
            BLOCK_SIZE,
            ByteSize::from_bytes(TEN_MIB_BYTES as u64),
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
                    let i = i.as_bytes() as usize;
                    raw[i..][..buf.len()].copy_from_slice(buf);
                    Ok(())
                },
                BLOCK_SIZE,
                ByteSize::from_bytes(TEN_MIB_BYTES as u64),
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

    /// Prevent adding overlapping partitions
    #[test]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    fn invalid_partitions() {
        let raw = data().unwrap();
        let mut gpt = read_gpt_size::<U128>(&raw).unwrap();
        let part = gpt.partitions()[0];
        let e = gpt.add_partition(part).unwrap_err();
        panic!(e.to_string());
    }
}

// TODO: Port these tests
#[cfg(any())]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use std::io::Cursor;
    use uuid::Uuid;

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
