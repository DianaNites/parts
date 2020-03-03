//! Gpt Definitions

mod error;
mod header;
mod partition;
mod raw;

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
