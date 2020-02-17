//! MBR definitions
use crate::types::*;
use displaydoc::Display;
use generic_array::{typenum::U440, GenericArray};
use serde::{Deserialize, Serialize};
use std::{
    convert::TryFrom,
    io::{prelude::*, SeekFrom},
};
use thiserror::Error;

// FIXME: Not ideal but :shrug:. QuirkBrokenPartedCHS needs it?
#[allow(clippy::large_enum_variant)]
#[derive(Error, Debug, Display)]
pub(crate) enum MbrError {
    /// Reading or writing the MBR failed.
    Io(#[from] std::io::Error),

    /// The MBR signature is invalid. (Expected: 0x55AA-LE, got: `{0:X?}`)
    InvalidMbrSignature([u8; 2]),

    /// The MBR has more partitions than it should.
    /// A GPT Protective MBR should only ever have one partition, with the
    /// GPT Protective OS type.
    InvalidPartitions,

    /// Unknown MBR error.
    Unknown,
}

type Result<T, E = MbrError> = std::result::Result<T, E>;

/// GPT Protective MBR
#[derive(Serialize, Deserialize, PartialEq)]
pub(crate) struct ProtectiveMbr {
    /// Bios boot code. Unused by GPT.
    boot_code: GenericArray<u8, U440>,

    /// A unique signature. Unused by GPT.
    /// Hard-coded to 0.
    unique_signature: [u8; 4],

    /// Hard-coded to 0.
    unknown: [u8; 2],

    /// Hard-coded to one partition, covering the entire device.
    partitions: [MbrPart; 4],

    /// Hard-coded to 0xAA55.
    signature: [u8; 2],
}

// Crate public
impl ProtectiveMbr {
    /// Creates a new Protective MBR
    ///
    /// `last_lba`, the last usable logical block address on the device.
    pub(crate) fn new(last_lba: LogicalBlockAddress) -> Self {
        Self {
            boot_code: GenericArray::default(),
            unique_signature: [0u8; 4],
            unknown: [0u8; 2],
            partitions: [
                MbrPart {
                    boot: 0,
                    //
                    start_head: 0x00,
                    start_sector: 0x02,
                    start_track: 0x00,
                    //
                    os_type: 0xEE,
                    // Technically incorrect, but
                    // Existing implementations seem to do the same thing here.
                    end_head: 0xFF,
                    end_sector: 0xFF,
                    end_track: 0xFF,
                    //
                    start_lba: 0x01,
                    size_lba: u32::try_from(last_lba.0).unwrap_or(u32::max_value()),
                },
                MbrPart::default(),
                MbrPart::default(),
                MbrPart::default(),
            ],
            signature: [0x55, 0xAA],
        }
    }

    /// Read a `ProtectiveMbr` from a `Read`er.
    ///
    /// # Errors
    ///
    /// - If the `Read`er errors.
    /// - If the MBR is invalid.
    /// - If an invalid MBR from GNU Parted is detected. This error is
    ///   recoverable.
    ///
    /// # Details
    ///
    /// On success, this will have read exactly `block_size` bytes.
    ///
    /// On error, the amount read is unspecified.
    pub(crate) fn from_reader<R: Read + Seek>(
        mut source: R,
        block_size: BlockSize,
    ) -> Result<Self> {
        let obj: Self = bincode::deserialize_from(&mut source).map_err(|err| match *err {
            bincode::ErrorKind::Io(e) => MbrError::Io(e),
            _ => MbrError::Unknown,
        })?;
        // Seek past the remaining block.
        source.seek(SeekFrom::Current(block_size.0 as i64 - 512))?;
        //
        obj.validate()
    }

    /// Write a GPT Protective MBR to a `Write`r.
    ///
    /// # Errors
    ///
    /// - If the `Write`r does.
    ///
    /// # Details
    ///
    /// On success, this will have written exactly `block_size` bytes.
    ///
    /// On error, the amount written is unspecified.
    pub(crate) fn to_writer<W: Write + Seek>(
        &self,
        mut dest: W,
        block_size: BlockSize,
    ) -> Result<()> {
        bincode::serialize_into(&mut dest, self).map_err(|err| match *err {
            bincode::ErrorKind::Io(e) => MbrError::Io(e),
            _ => MbrError::Unknown,
        })?;
        // Account for reserved space.
        let len = (block_size.0 - 512) as usize;
        dest.write_all(&vec![0; len])?;
        Ok(())
    }
}

// Private
impl ProtectiveMbr {
    /// Validate the Protective MBR.
    ///
    /// # Details
    ///
    /// - Ensures the signature is correct.
    /// - Ensures
    /// - Ensures there are no other partitions.
    ///
    /// This will also silently fix a GNU Parted bug
    /// where the `start_sector` is 0x01 instead of 0x02,
    /// and the `end_head` is 0xFE instead of 0xFF.
    fn validate(mut self) -> Result<Self> {
        if !(self.signature[0] == 0x55 && self.signature[1] == 0xAA) {
            return Err(MbrError::InvalidMbrSignature(self.signature));
        }
        let part: &mut MbrPart = &mut self.partitions[0];
        if part.os_type != 0xEE {
            return Err(MbrError::InvalidPartitions);
        }

        // NOTE: Fixes a GNU Parted bug.
        if part.start_sector == 0x01 || part.end_head == 0xFE {
            part.start_sector = 0x02;
            part.end_head = 0xFF;
        }

        if !(part.start_head == 0x00 && part.start_sector == 0x02 && part.start_track == 0x00) {
            return Err(MbrError::InvalidPartitions);
        };

        if !(part.end_head == 0xFF && part.end_sector == 0xFF && part.end_track == 0xFF) {
            return Err(MbrError::InvalidPartitions);
        };

        for part in &self.partitions[1..] {
            if *part != MbrPart::default() {
                return Err(MbrError::InvalidPartitions);
            }
        }
        Ok(self)
    }
}

/// Smaller Debug output.
impl std::fmt::Debug for ProtectiveMbr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("ProtectiveMbr")
            .field("partition 0", &self.partitions[0])
            .finish()
    }
}

#[derive(Debug, Default, Serialize, Deserialize, PartialEq)]
struct MbrPart {
    /// Whether the partition is "bootable". Unused by GPT.
    /// Hard-coded to 0.
    boot: u8,

    /// Cylinder, Head, Sector. Unused by GPT.
    /// Hard-coded to 0x000200.
    start_head: u8,
    start_sector: u8,
    start_track: u8,

    /// Hard-coded to 0xEE, GPT Protective.
    os_type: u8,

    /// Cylinder, Head, Sector. Unused by GPT.
    /// De facto Hard-coded to 0xFFFFFF.
    end_head: u8,
    end_sector: u8,
    end_track: u8,

    /// Hard-coded to 1, the start of the GPT Header.
    start_lba: u32,

    /// Size of the disk, in LBA, minus one. So the last *usable* LBA.
    size_lba: u32,
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result as AResult;
    use static_assertions::*;
    use std::io::Cursor;

    const TEST_PARTS_CF: &str = "tests/data/test_parts_cf";
    const BLOCK_SIZE: BlockSize = BlockSize(512);

    type Result = AResult<()>;

    assert_eq_size!(MbrPart, [u8; 16]);
    assert_eq_size!(ProtectiveMbr, [u8; 512]);

    /// Basic reading should work and validate correctly.
    #[test]
    fn read_test() -> Result {
        let mut data = Cursor::new(vec![0; BLOCK_SIZE.0 as usize]);
        let mut file = std::fs::File::open(TEST_PARTS_CF)?;
        file.read_exact(data.get_mut())?;
        //
        let _mbr = ProtectiveMbr::from_reader(data, BLOCK_SIZE)?;
        //
        Ok(())
    }
}
