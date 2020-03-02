//! Raw Gpt stuff
use super::{header::*, partition::*};
use crate::{mbr::ProtectiveMbr, types::*};
use generic_array::{
    typenum::{Unsigned, U128},
    ArrayLength,
    GenericArray,
};
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
    /// `partitions` will be called for every partition in the GPT.
    ///
    /// As an argument it receives the byte offset of the partition entry,
    /// a buffer capable of holding each partition entry.
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
                // This is okay because we use read_unaligned
                #[allow(clippy::cast_ptr_alignment)]
                let _part = unsafe { (source.as_ptr() as *const RawPartition).read_unaligned() };
                if i < partitions.len() {
                    partitions[i] = Partition::default();
                }
            },
        )?;

        Ok(Gpt {
            uuid: primary.uuid,
            partitions,
        })
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

    #[test]
    fn read_gpt() -> Result {
        let raw = data()?;
        read_gpt_size::<U128>(&raw)?;
        read_gpt_size::<U0>(&raw)?;
        read_gpt_size::<U64>(&raw)?;
        read_gpt_size::<U128>(&raw)?;
        read_gpt_size::<U256>(&raw)?;
        //
        Ok(())
    }
}
