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
}

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
