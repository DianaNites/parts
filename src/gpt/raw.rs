//! Raw Gpt stuff
use super::{error::*, header::*, partition::*};
use crate::{
    mbr::{ProtectiveMbr, MBR_SIZE},
    types::*,
};
use crc::{crc32, Hasher32};
use generic_array::{
    typenum::{Unsigned, U128},
    ArrayLength,
    GenericArray,
};
#[cfg(any(feature = "std", test))]
use std::io::prelude::*;
#[cfg(any(feature = "std", test))]
use std::io::SeekFrom;
use uuid::Uuid;

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
    /// `func` will be called for every partition in the GPT.
    ///
    /// As an argument it receives the byte offset of the partition entry,
    /// and a buffer capable of holding each partition entry.
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

    /// Write the full GPT
    ///
    /// ~~`primary` must contain LBA0 and LBA1. That is, `block_size * 2`
    /// bytes.~~
    ///
    /// ~~`alt` must be the last LBA. That is, `block_size` bytes.~~
    ///
    /// `disk_size` must be the size of the device.
    ///
    /// `func` will be called for every partition in the GPT.
    ///
    /// As an argument it receives the byte offset to write at, and
    /// a buffer holding each partition entry, which must be written.
    ///
    /// It returns a [`Result`]<()>, and errors are propagated.
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
    pub fn to_bytes<F: FnMut(ByteSize, &[u8]) -> Result<()>>(
        &self,
        func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<()> {
        self.to_bytes_with_size(func, block_size, disk_size)
    }

    #[cfg(any(feature = "std", test))]
    pub fn from_reader<RS: Read + Seek>(
        source: RS,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<Self> {
        Gpt::from_reader_with_size(source, block_size, disk_size)
    }

    #[cfg(any(feature = "std", test))]
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
    /// FIXME: Wrong, we ignore after the last one and assume it's zero.
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
        validate(
            &primary,
            &alt,
            &mut func,
            block_size,
            disk_size,
            |i, source| {
                if i < partitions.len() {
                    partitions[i] = Partition::from_bytes(source);
                }
            },
        )?;

        Ok(Gpt {
            uuid: primary.uuid,
            partitions,
        })
    }

    /// Like [`Gpt::to_bytes`] but stores `N` partitions.
    ///
    /// See [`Gpt::from_bytes_with_size`] for more details.
    // TODO: When partition validity checks are done, they'll need to be rechecked
    // here. Make sure all partitions are within disk_size/usable blocks
    pub fn to_bytes_with_size<F: FnMut(ByteSize, &[u8]) -> Result<()>>(
        &self,
        mut func: F,
        block_size: BlockSize,
        disk_size: ByteSize,
    ) -> Result<()> {
        let last_lba = (disk_size / block_size) - 1;
        let mut mbr = ProtectiveMbr::new(last_lba);
        let mut mbr_buf = [0; MBR_SIZE];
        mbr.write_bytes(&mut mbr_buf, block_size)
            .map_err(|_| Error::Invalid("Couldn't write protective MBR"))?;
        func(ByteSize::from_bytes(0), &mbr_buf)?;
        //
        let mut header_buf = [0; HEADER_SIZE as usize];
        let mut partition_buf = [0; PARTITION_ENTRY_SIZE as usize];
        let mut parts = 0;
        let mut digest = crc32::Digest::new(crc32::IEEE);
        for part in self.partitions {
            if part == Partition::default() {
                continue;
            }
            part.to_bytes(&mut partition_buf);
            digest.write(&partition_buf);
            parts += 1;
        }
        let parts_crc = digest.sum32();
        let disk_uuid = self.uuid;

        let alt = Header::new(
            last_lba,
            LogicalBlockAddress(1),
            parts,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        alt.to_bytes(&mut header_buf)?;
        func(last_lba * block_size, &header_buf)?;
        for (i, part) in self.partitions.into_iter().enumerate() {
            if part == Partition::default() {
                continue;
            }
            part.to_bytes(&mut partition_buf);
            let b = alt.array * block_size;
            let b = b + (ByteSize::from_bytes(PARTITION_ENTRY_SIZE as u64) * i as u64);
            func(b, &partition_buf)?;
        }
        //
        let primary = Header::new(
            LogicalBlockAddress(1),
            last_lba,
            parts,
            parts_crc,
            disk_uuid,
            block_size,
            disk_size,
        );
        primary.to_bytes(&mut header_buf)?;
        func(LogicalBlockAddress(1) * block_size, &header_buf)?;
        for (i, part) in self.partitions.into_iter().enumerate() {
            if part == Partition::default() {
                continue;
            }
            part.to_bytes(&mut partition_buf);
            let b = primary.array * block_size;
            let b = b + (ByteSize::from_bytes(PARTITION_ENTRY_SIZE as u64) * i as u64);
            func(b, &partition_buf)?;
        }
        Ok(())
    }

    ///
    #[cfg(any(feature = "std", test))]
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

    ///
    #[cfg(any(feature = "std", test))]
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
    N: Unsigned,
    N: ArrayLength<Partition>,
    N::ArrayType: Copy,
{
    pub fn uuid(&self) -> Uuid {
        self.uuid
    }

    /// Slice of in-use partitions
    pub fn partitions(&self) -> &[Partition] {
        let len = self
            .partitions
            .iter()
            .filter(|p| **p != Partition::default())
            .count();
        &self.partitions[..len]
    }

    /// Mutable slice of in-use partitions.
    pub fn partitions_mut(&mut self) -> &mut [Partition] {
        let len = self
            .partitions
            .iter()
            .filter(|p| **p != Partition::default())
            .count();
        &mut self.partitions[..len]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use generic_array::{
        typenum::{Unsigned, U0, U128, U256, U64},
        ArrayLength,
    };
    use static_assertions::*;
    use std::io::Cursor;

    assert_eq_size!(RawPartition, [u8; PARTITION_ENTRY_SIZE as usize]);

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
        )?;
        //
        Ok(gpt)
    }

    /// Test that we can read a GPT from another tool
    #[test]
    fn read_gpt() -> Result {
        let raw = data()?;
        let gpt = read_gpt_size::<U128>(&raw)?;
        read_gpt_size::<U0>(&raw)?;
        read_gpt_size::<U64>(&raw)?;
        read_gpt_size::<U256>(&raw)?;
        //
        assert_eq!(gpt.partitions().len(), 1);
        assert_eq!(
            gpt.partitions()[0].uuid(),
            Uuid::parse_str(CF_PART_GUID).unwrap()
        );
        assert_eq!(gpt.uuid, Uuid::parse_str(CF_DISK_GUID).unwrap());
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
    fn std_gpt_test() -> Result {
        let raw = data()?;
        let raw = Cursor::new(raw);
        let gpt = Gpt::from_reader(raw, BLOCK_SIZE, ByteSize::from_bytes(TEN_MIB_BYTES as u64))?;
        // FIXME: Duplicate of `read_gpt`? Keep in sync? Extract function?
        assert_eq!(gpt.partitions().len(), 1);
        assert_eq!(
            gpt.partitions()[0].uuid(),
            Uuid::parse_str(CF_PART_GUID).unwrap()
        );
        assert_eq!(gpt.uuid, Uuid::parse_str(CF_DISK_GUID).unwrap());
        //
        Ok(())
    }

    /// Don't panic on slice indexing if given an empty slice?
    #[test]
    #[ignore]
    fn empty_bytes_regress() {
        read_gpt_size::<U128>(&[]).unwrap();
    }
}
