//! Gpt Definitions
use crate::types::*;
use displaydoc::Display;
#[cfg(feature = "std")]
use std::io::{prelude::*, SeekFrom};
#[cfg(feature = "std")]
use thiserror::Error;

mod error;
mod header;
mod partition;
mod raw;

/// GPT Error Type.
#[derive(Debug, Display)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum NewGptError {
    #[cfg(feature = "std")]
    /// Reading or writing the GPT failed
    Io(#[from] std::io::Error),

    /// Both the Primary and Backup GPT header are corrupt or non-existent.
    InvalidGpt,

    /// The size of the device does not match what the GPT Header expects.
    /// (expected: {0}, got {1})
    ///
    /// Use `Gpt::` to resolve this.
    InvalidDiskSize(ByteSize, ByteSize),

    /// Not enough data was provided
    NotEnough,

    /// Unknown Error
    Unknown,
}

type Result<T, E = NewGptError> = core::result::Result<T, E>;

/// A GPT Disk
///
///
/// All modifications are done in-memory and
/// the *only* method that will modify a real device/file is
/// [`Gpt::to_writer`].
///
/// # Usage
///
/// See [`Gpt::new`] and [`Gpt::from_reader`]
///
/// # Panics
///
/// It is possible to create an invalid [`Gpt`] instance,
/// for the purposes of repairing it.
///
/// Using such an instance without repairing it may cause certain methods to
/// panic. The only method safe to use is [`Gpt::repair`].
#[derive(Debug)]
// Comparing this doesn't make sense except in tests.
#[cfg_attr(test, derive(PartialEq))]
pub struct Gpt {}

#[cfg(any())]
/// Methods Creating and Writing out the GPT
impl Gpt {
    /// Create a new GPT label,
    /// assuming a size of `disk_size` and a block size of `block_size`
    ///
    /// This creates a valid, but empty, Gpt Label.
    ///
    /// # Examples
    ///
    /// Create a new Gpt Table and add a partition.
    ///
    /// ```rust
    /// # use parts::{Gpt, GptPartBuilder};
    /// # use parts::types::*;
    /// # let block_size = BlockSize(512);
    /// # let disk_size = (block_size * 100).into();
    /// let mut gpt = Gpt::new(block_size, disk_size);
    /// let part = GptPartBuilder::new(block_size)
    ///     .name("Example")
    ///     .size((block_size * 2).into())
    ///     .start(LogicalBlockAddress(34))
    ///     .finish();
    /// gpt.add_partition(part);
    /// ```
    ///
    /// # Panics
    ///
    /// - If `disk_size` isn't large enough.
    ///
    /// Specifically, `disk_size` must be large enough to fit
    /// the GPT Header, the minimum required Gpt Partition array,
    /// and their backups.
    ///
    /// For a `block_size` of 512, this is 512 * 67.
    /// Two blocks at the start, the MBR and GPT header,
    /// 32 blocks for the partition array, one for the backup GPT header,
    /// and 32 blocks for the backup partition array.
    ///
    /// Note that such a small size has no room for any partitions.
    pub fn new(block_size: BlockSize, disk_size: ByteSize) -> Self {
        // logical block addresses start at zero.
        let last_lba = (disk_size / block_size) - 1;
        let min_partition_blocks = ByteSize::from_bytes(MIN_PARTITIONS_BYTES) / block_size;
        //
        assert!(
            (last_lba + 1) >= ((min_partition_blocks * 2) + 3),
            "disk_size is too small to hold the GPT"
        );
        //
        let _mbr = ProtectiveMbr::new(last_lba);
        //
        // let mut header = GptHeader::new();
        // header.this_lba = 1.into();
        // header.alt_lba = last_lba;
        // // Plus two blocks, one for the MBR and one for the GPT Header.
        // header.first_usable_lba = min_partition_blocks + 2;
        // // Minus 1 block for the GPT Header
        // header.last_usable_lba = last_lba - min_partition_blocks - 1;
        // header.partition_array_start = 2.into();
        // // header.header_crc32 = calculate_crc(&header);
        // //
        // let mut backup: GptHeader = header.clone();
        // backup.this_lba = last_lba;
        // backup.alt_lba = 1.into();
        // // usable addresses are not inclusive
        // backup.partition_array_start = backup.last_usable_lba + 1;
        // backup.header_crc32 = 0;
        // // backup.header_crc32 = calculate_crc(&backup);
        // //
        // let header = Some(header);
        // let backup = Some(backup);
        //
        Self {
            // header,
            // backup,
            partitions: Default::default(),
            block_size,
            disk_size,
        }
    }

    /// Read a GPT label from a byte slice
    ///
    /// # Errors
    ///
    /// - If `source` does not have enough data
    /// - The GPT is invalid.
    pub fn from_bytes(mut source: &[u8], block_size: BlockSize) -> Result<Self> {
        let b_size = block_size.0.try_into().unwrap();
        if source.len() < b_size {
            return Err(NewGptError::NotEnough);
        }
        // Safe because ProtectiveMBR
        let _mbr = ProtectiveMbr::from_bytes(&mut source, block_size)
            .map_err(|_| NewGptError::InvalidGpt)?;
        todo!()
    }

    /// Read from an existing GPT Disk or image.
    ///
    /// # Examples
    ///
    /// Read from an in-memory representation.
    ///
    /// ```rust
    /// # use std::io::Cursor;
    /// # use parts::Gpt;
    /// # use parts::types::*;
    /// # const TEN_MIB_BYTES: usize = 10485760;
    /// # const BLOCK_SIZE: BlockSize = BlockSize(512);
    /// let mut data = Cursor::new(vec![0; TEN_MIB_BYTES]);
    /// let gpt = Gpt::from_reader(&mut data, BLOCK_SIZE);
    /// ```
    ///
    /// # Errors
    ///
    /// - If IO fails.
    /// - If the Protective MBR is invalid.
    /// - If the primary and/or backup GPT is invalid.
    ///
    /// ## Invalid GPT Headers
    ///
    /// In this case the [`Err`] variant will contain a [`Gpt`] Instance,
    /// which should be repaired after asking permission from the user.
    ///
    /// If both the primary and backup GPT is corrupt, repairing will not be
    /// possible.
    #[cfg(feature = "!std")]
    pub fn from_reader<RS>(mut source: RS, block_size: BlockSize) -> Result<Self>
    where
        RS: Read + Seek,
    {
        let disk_size: ByteSize = {
            let cur = source.seek(SeekFrom::Current(0))?;
            let end = ByteSize::from_bytes(source.seek(SeekFrom::End(0))?);
            source.seek(SeekFrom::Start(cur))?;
            end
        };
        //
        let mbr = ProtectiveMbr::from_reader(&mut source, block_size).map_err(|err| match err {
            MbrError::Io(e) => NewGptError::Io(e),
            _ => NewGptError::Unknown,
        })?;
        //
        let header_lba = LogicalBlockAddress(source.seek(SeekFrom::Current(0))? / block_size.0);
        // let header = GptHeader::from_reader(&mut source, block_size);

        // Seek to the last LBA
        source.seek(SeekFrom::End(-(block_size.0 as i64)))?;

        let backup_lba = LogicalBlockAddress(source.seek(SeekFrom::Current(0))? / block_size.0);
        // let backup = GptHeader::from_reader(&mut source, block_size).and_then(|mut
        // header| {     // match check(&mut header, backup_lba, header_lba) {
        //     //     Ok(_) => Ok(header),
        //     //     Err(e) => Err(e),
        //     // }
        //     todo!()
        // });
        //
        // let header = header.and_then(|mut header| {
        //     todo!();
        //     // match check(&mut header, header_lba, backup_lba) {
        //     //     Ok(_) => Ok(header),
        //     //     Err(e) => Err(e),
        //     // }
        // });
        //
        assert_eq!(header_lba, LogicalBlockAddress(1));

        let (header, backup) = match (header, backup) {
            // Both headers corrupt, return error.
            (Err(_), Err(_)) => return Err(NewGptError::InvalidGpt),
            // One of the headers is corrupt.
            (Ok(h), Err(_)) => (Some(h), None),
            (Err(_), Ok(b)) => (None, Some(b)),
            // Both headers are fine.
            (Ok(h), Ok(b)) => (Some(h), Some(b)),
        };

        let mut obj: Self = Self {
            mbr,
            header,
            backup,
            partitions: Vec::new(),
            block_size,
            disk_size,
        };

        if let Some(header) = &mut obj.header {
            obj.partitions.reserve_exact(header.partitions as usize);
            //
            let start = header.partition_array_start * block_size;
            let start = start.as_bytes();
            source.seek(SeekFrom::Start(start))?;
            //
            for _ in 0..header.partitions {
                let part = GptPart::from_reader(&mut source, header.partition_size)?;
                obj.partitions.push(part);
            }
            let crc = 0; //calculate_part_crc(&obj.partitions);
            assert_eq!(crc, header.partitions_crc32);
        } else if let Some(backup) = &mut obj.backup {
            obj.partitions.reserve_exact(backup.partitions as usize);
            //
            let start = backup.partition_array_start * block_size;
            let start = start.as_bytes();
            source.seek(SeekFrom::Start(start))?;
            //
            for _ in 0..backup.partitions {
                let part = GptPart::from_reader(&mut source, backup.partition_size)?;
                obj.partitions.push(part);
            }
            let crc = 0; //calculate_part_crc(&obj.partitions);
            assert_eq!(crc, backup.partitions_crc32);
        }

        Ok(obj)
    }

    /// Write the GPT structure to a [`Write`]r.
    ///
    /// # Errors
    ///
    /// - If IO does.
    /// - If `dest` is a different size than expected.
    /// GPT requires that the last logical block address be
    /// the backup GPT Header. If `dest` has grown larger, both headers
    /// will need updating.
    ///
    /// # Panics
    ///
    /// - If this [`Gpt`] instance is corrupt.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use parts::Gpt;
    /// # use parts::types::*;
    /// use std::io::Cursor;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let block_size = BlockSize(512);
    /// # let disk_size = (block_size * 100).into();
    /// let gpt = Gpt::new(block_size, disk_size);
    /// let mut buffer = Cursor::new(vec![0; disk_size.as_bytes() as usize]);
    /// gpt.to_writer(&mut buffer)?;
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(feature = "!std")]
    pub fn to_writer<W: Write + Seek>(&self, mut dest: W) -> Result<()> {
        let header = todo!(); //self.header.as_ref().unwrap();
        let backup = todo!(); //self.backup.as_ref().unwrap();
                              //
        let disk_size = {
            let cur = dest.seek(SeekFrom::Current(0))?;
            let end = dest.seek(SeekFrom::End(0))?;
            dest.seek(SeekFrom::Start(cur))?;
            ByteSize::from_bytes(end)
        };
        if disk_size != self.disk_size {
            return Err(NewGptError::InvalidDiskSize(self.disk_size, disk_size));
        }
        //
        self.mbr
            .to_writer(&mut dest, self.block_size)
            .map_err(|e| match e {
                MbrError::Io(e) => NewGptError::Io(e),
                _ => NewGptError::Unknown,
            })?;

        header.to_writer(&mut dest, self.block_size.0)?;

        dest.seek(SeekFrom::Start(
            (header.partition_array_start * self.block_size).as_bytes(),
        ))?;
        for part in &self.partitions {
            part.to_writer(&mut dest, header.partition_size)?;
        }

        dest.seek(SeekFrom::Start(
            (header.alt_lba * self.block_size).as_bytes(),
        ))?;
        backup.to_writer(&mut dest, self.block_size.0)?;

        dest.seek(SeekFrom::Start(
            (backup.partition_array_start * self.block_size).as_bytes(),
        ))?;
        for part in &self.partitions {
            part.to_writer(&mut dest, backup.partition_size)?;
        }

        //
        Ok(())
    }
}

#[cfg(any())]
/// Methods for handling partitions
impl Gpt {
    /// Iterator of the available partitions.
    pub fn partitions(&self) -> &[GptPart] {
        &self.partitions
    }

    /// Adds a new partition
    ///
    /// # Examples
    ///
    /// See [`Gpt::new`]
    ///
    /// # Panics
    ///
    /// - If the [`GptPart`] doesn't fit
    /// within the first/last usable logical block addresses.
    /// - If `part` overlaps with any existing partition.
    pub fn add_partition(&mut self, part: GptPart) {
        let header = todo!(); //self.header.as_mut().unwrap();
        let backup = todo!(); //self.backup.as_mut().unwrap();
                              //
        assert!(
            part.starting_lba >= header.first_usable_lba,
            "Invalid Partition Span: {:?}",
            (part.starting_lba, part.ending_lba)
        );
        assert!(
            part.ending_lba <= header.last_usable_lba,
            "Invalid Partition Span: {:?}",
            (part.starting_lba, part.ending_lba)
        );
        for existing in &self.partitions {
            if part.starting_lba >= existing.starting_lba
                && part.starting_lba <= existing.ending_lba
            {
                panic!(
                    "Attempted to add overlapping partitions. `{:#?}` overlaps with `{:#?}`",
                    part, existing
                );
            }
        }
        // FIXME: Support more partitions.
        // This would require moving the first usable lba forward, and the last usable
        // one back.
        assert!(header.partitions <= 128, "Too many partitions");
        // TODO: Partition push
        // self.partitions.push(part);
        // `GptHeader::partitions` can be larger than the
        // actual number of partitions, at least in practice.
        if self.partitions.len() > header.partitions as usize {
            header.partitions += 1;
            backup.partitions += 1;
        }
        //
        self.recalculate_part_crc();
    }

    /// Remove an existing partition at the index `index`.
    ///
    /// Returns the removed partition.
    /// This allows you to modify it using [`GptPartBuilder::from_part`] and
    /// then re-add it.
    ///
    /// Note that indexing starts at zero.
    ///
    /// # Panics
    ///
    /// - If `index` is out of bounds.
    pub fn remove_partition(&mut self, index: usize) -> GptPart {
        // TODO: Partition remove
        todo!()
        // self.partitions.swap_remove(index)
    }

    /// Get the first logical block address you can use for partitions.
    /// This is useful with [`GptPartBuilder`]
    pub fn first_usable_address(&self) -> LogicalBlockAddress {
        // self.header.as_ref().unwrap().first_usable_lba
        todo!()
    }

    /// Get the last logical block address you can use for partitions.
    /// This is useful with [`GptPartBuilder`]
    pub fn last_usable_address(&self) -> LogicalBlockAddress {
        // self.header.as_ref().unwrap().last_usable_lba
        todo!()
    }

    /// Returns the remaining size on disk for a partition starting at
    /// the `start` [`LogicalBlockAddress`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use parts::*;
    /// # use parts::types::*;
    /// # let block_size = BlockSize(512);
    /// let image_size = ByteSize::from_mib(100);
    ///
    /// let gpt = Gpt::new(block_size, image_size);
    /// let first_part = GptPartBuilder::new(block_size)
    ///     .name("First")
    ///     .size(ByteSize::from_mib(1))
    ///     .start(ByteSize::from_mib(1) / block_size)
    ///     .finish();
    /// let remaining_part = GptPartBuilder::new(block_size)
    ///     .name("Remaining")
    ///     .size(gpt.remaining(first_part.end() + 1))
    ///     .start(first_part.end() + 1)
    ///     .finish();
    /// let part_size = ((remaining_part.end() - remaining_part.start()) + 1) * block_size;
    ///
    /// // 1MiB for padding, then 1MiB for `first_part`,
    /// // and then 17 * 2(34KiB) for the GPT headers.
    /// let expected_remaining = ByteSize::from_mib(98) - (ByteSize::from_kib(17) * 2);
    ///
    /// assert_eq!(part_size, expected_remaining)
    /// ```
    pub fn remaining(&self, start: LogicalBlockAddress) -> ByteSize {
        ((self.last_usable_address() - self.first_usable_address()) - start) * self.block_size
    }
}

#[cfg(any())]
impl Gpt {
    /// Set the disk GUID.
    ///
    /// # Safety
    ///
    /// This is unsafe because GPT Disk GUID's are supposed to be unique.
    ///
    /// Having two disks with the same GUID is a violation of the spec.
    pub unsafe fn set_disk_guid(&mut self, new_guid: Uuid) {
        let new_guid = uuid_hack(new_guid);
        //
        // self.header.as_mut().unwrap().disk_guid = new_guid;
        // self.backup.as_mut().unwrap().disk_guid = new_guid;
        self.recalculate_crc();
    }

    /// Repair an invalid GPT instance.
    ///
    /// An invalid GPT instance is one with a corrupt or missing
    /// backup or primary label.
    ///
    /// Repairing such an instance involves duplicating the existing label
    /// and replacing the corrupt area.
    ///
    /// Only call this method with permission from the user.
    ///
    /// # Examples
    ///
    /// Pseudo-code showing how to repair a corrupt [`Gpt`]
    ///
    /// ```rust,compile_fail
    /// let corrupt_gpt = Gpt::from_reader(Cursor::new(&mut corrupted_buf), BLOCK_SIZE);
    /// match corrupt_gpt {
    ///     Err(GptError::CorruptGpt(mut gpt, _)) => {
    ///         assert_eq!(gpt.header, None);
    ///         assert_eq!(gpt.backup, Some(_));
    ///         gpt.repair();
    ///         assert_eq!(gpt.header, uncorrupted_gpt.header);
    ///     }
    /// }
    /// ```
    pub fn repair(&mut self) {
        if self.header.is_none() || self.backup.is_none() {
            let last_lba = (self.disk_size / self.block_size) - 1;
            if let Some(header) = &self.header {
                let mut backup = header.clone();
                backup.this_lba = last_lba;
                backup.alt_lba = 1.into();
                backup.partition_array_start = header.last_usable_lba + 1;
                backup.header_crc32 = 0;
                // backup.header_crc32 = calculate_crc(&backup);
                self.backup = Some(backup);
            } else if let Some(backup) = &self.backup {
                let mut header = backup.clone();
                header.this_lba = 1.into();
                header.alt_lba = last_lba;
                header.partition_array_start = 2.into();
                header.header_crc32 = 0;
                // header.header_crc32 = calculate_crc(&header);
                self.header = Some(header);
            }
        }
    }

    /// If the underlying device has somehow grown larger,
    /// you won't be able to use [`Gpt::to_writer`].
    ///
    /// This will update the GPT and allow it to be written.
    pub fn update_disk_size(&mut self, new_size: ByteSize) {
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        self.disk_size = new_size;
        let min_partition_blocks = ByteSize::from_bytes(MIN_PARTITIONS_BYTES) / self.block_size;
        let last_lba = (self.disk_size / self.block_size) - 1;
        //
        header.last_usable_lba = last_lba - min_partition_blocks - 1;
        backup.this_lba = last_lba;
        self.recalculate_crc();
    }
}

#[cfg(any())]
// Private
impl Gpt {
    /// Recalculate the primary and backup header crc
    fn recalculate_crc(&mut self) {
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        header.header_crc32 = 0;
        // header.header_crc32 = calculate_crc(&header);
        //
        backup.header_crc32 = 0;
        // backup.header_crc32 = calculate_crc(&backup);
    }

    /// Recalculate the primary and backup partition crc.
    ///
    /// This also calls [`Gpt::recalculate_crc`], since updating the partition
    /// crc means the header one must be updated too.
    fn recalculate_part_crc(&mut self) {
        let source_bytes = unsafe {
            slice::from_raw_parts(
                self.partitions.as_ptr() as *const u8,
                mem::size_of::<GptPart>() * self.partitions.len(),
            )
        };
        let crc = crc32::checksum_ieee(&source_bytes);
        //
        let header = self.header.as_mut().unwrap();
        let backup = self.backup.as_mut().unwrap();
        //
        header.partitions_crc32 = crc;
        backup.partitions_crc32 = crc;
        //
        self.recalculate_crc();
    }
}

#[cfg(any())]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{Result, *};
    use std::io::Cursor;
    use uuid::Uuid;

    /// Tests that we can read an external GPT layout,
    /// serialize it, and deserialize it again, with it staying the same.
    #[test]
    fn gpt_roundtrip() -> Result {
        let file = std::fs::File::open(TEST_PARTS)?;
        //
        let src_gpt = Gpt::from_reader(file, BLOCK_SIZE)?;
        //
        let mut buf = Cursor::new(vec![0; TEN_MIB_BYTES]);
        src_gpt.to_writer(&mut buf)?;
        buf.set_position(0);
        //
        let new_gpt = Gpt::from_reader(&mut buf, BLOCK_SIZE)?;
        assert_eq!(src_gpt, new_gpt);
        //
        Ok(())
    }

    /// Tests that round-tripping gives us the exact bytes we got in
    #[test]
    #[ignore]
    fn exact_bytes() -> Result {
        let mut file = std::fs::File::open(TEST_PARTS)?;
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf)?;
        //
        let src_gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE)?;
        //
        let mut buf = Cursor::new(vec![0; TEN_MIB_BYTES]);
        src_gpt.to_writer(&mut buf).unwrap();
        //
        let v = buf.get_mut();
        assert_eq!(v.len(), TEN_MIB_BYTES);
        assert_eq!(v.len(), src_buf.len());
        assert_eq!(*v, src_buf);
        //
        Ok(())
    }

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

    /// Test that we don't crash on header sizes
    /// larger than the block size, or larger than [`GptHeader`]
    #[test]
    fn large_header_size() -> Result {
        let disk_size = BLOCK_SIZE * 100;
        let mut gpt = Gpt::new(BLOCK_SIZE, disk_size.into());
        let header = gpt.header.as_mut().unwrap();
        let backup = gpt.backup.as_mut().unwrap();
        header.header_size = (BLOCK_SIZE * 2).0 as u32;
        backup.header_size = (BLOCK_SIZE * 2).0 as u32;
        // Don't recalculate the crc32 here, because the problem we're testing
        // comes *from* calculating the crc32.
        //
        let mut v = Cursor::new(vec![0; disk_size.0 as usize]);
        gpt.to_writer(&mut v)?;
        let gpt = Gpt::from_reader(&mut v, BLOCK_SIZE).unwrap_err();
        dbg!(&gpt);
        Ok(())
    }

    /// Test large block sizes
    #[test]
    fn large_block_size() -> Result {
        let disk_size = LARGE_BLOCK_SIZE * 100;
        let gpt = Gpt::new(LARGE_BLOCK_SIZE, disk_size.into());
        dbg!(&gpt);
        let header = gpt.header.as_ref().unwrap();
        let backup = gpt.backup.as_ref().unwrap();
        assert!(header.first_usable_lba >= LogicalBlockAddress(6));
        assert!(backup.first_usable_lba >= LogicalBlockAddress(6));
        Ok(())
    }

    /// Ensure that [`Gpt::new`] panics if the disk is too small.
    #[test]
    #[should_panic(expected = "disk_size is too small")]
    fn small_disk() {
        let disk_size = BLOCK_SIZE * 30;
        let _gpt = Gpt::new(BLOCK_SIZE, disk_size.into());
    }

    /// Ensure that [`Gpt::new`] doesn't panics if the disk is
    /// exactly the minimum size.
    ///
    /// Prevent an off-by-one error in minimum size checking.
    #[test]
    fn minimum_disk_regress() {
        let disk_size = BLOCK_SIZE * 67;
        let _gpt = Gpt::new(BLOCK_SIZE, disk_size.into());
    }

    /// Ensure that the GPT can properly be repaired if only one header is
    /// corrupt.
    #[test]
    #[ignore]
    fn corrupt_gpt_test() {
        let mut file = std::fs::File::open(TEST_PARTS_CF).unwrap();
        let mut src_buf = Vec::with_capacity(TEN_MIB_BYTES);
        file.read_to_end(&mut src_buf).unwrap();
        //
        let _src_gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE).unwrap();
        // Invalidate the primary GPT
        src_buf[512] = 0;
        //
        let _gpt = Gpt::from_reader(Cursor::new(&mut src_buf), BLOCK_SIZE);
        // match gpt {
        //     Err(GptError::CorruptGpt(mut gpt, _)) => {
        //         assert_eq!(gpt.header, None);
        //         gpt.repair();
        //         dbg!(&gpt.header);
        //         dbg!(&src_gpt.header);
        //         assert_eq!(gpt.header, src_gpt.header);
        //     }
        //     g => {
        //         dbg!(&g);
        //         eprintln!("{}", g.unwrap_err());
        //         panic!("`corrupt_gpt_test` unexpected error");
        //     }
        // }
    }

    /// Ensure that [`Gpt::from_reader`] properly fails if there is no
    /// primary or backup Gpt.
    #[test]
    #[should_panic]
    fn missing_gpt_test() {
        let data = Cursor::new(vec![0; TEN_MIB_BYTES]);
        let _gpt = Gpt::from_reader(data, BlockSize(512)).unwrap();
    }

    #[test]
    #[should_panic(expected = "Attempted to add overlapping partitions")]
    fn invalid_partitions() {
        let mut gpt = Gpt::new(BLOCK_SIZE, ByteSize::from_bytes(TEN_MIB_BYTES as u64));
        let part = GptPartBuilder::new(BLOCK_SIZE)
            .size(ByteSize::from_mib(8))
            .start(ByteSize::from_mib(1) / BLOCK_SIZE)
            .part_type(LINUX_PART_GUID)
            .finish();
        let dup_part = part.clone();
        gpt.add_partition(part);
        gpt.add_partition(dup_part);
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
