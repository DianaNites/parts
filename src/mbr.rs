//! MBR definitions
use crate::util::*;
use serde::{Deserialize, Serialize};
use snafu::{ensure, ResultExt, Snafu};
use std::io::{prelude::*, SeekFrom};

#[derive(Debug, Snafu)]
pub(crate) enum MbrError {
    #[snafu(display("Invalid MBR Signature: {:?}", signature))]
    Signature { signature: [u8; 2] },

    #[snafu(display("Not a Protective MBR, has other partitions"))]
    Validation {},

    #[snafu(display("Error parsing MBR Header structure"))]
    Parse { source: bincode::Error },

    #[snafu(display("Error reading from device"))]
    Io { source: std::io::Error },
}

type Result<T, E = MbrError> = std::result::Result<T, E>;

/// GPT Protective MBR
#[derive(Serialize, Deserialize, PartialEq)]
pub(crate) struct ProtectiveMbr {
    /// Bios boot code. Unused by GPT.
    #[serde(with = "mbr_boot_code")]
    boot_code: Vec<u8>,

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

impl ProtectiveMbr {
    /// Creates a new Protective MBR
    ///
    /// ## Arguments
    ///
    /// - `last_lba`, the last logical block address on the device.
    pub(crate) fn new(last_lba: u64) -> Self {
        let last_lba = last_lba - 1;
        Self {
            boot_code: vec![0; 440],
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
                    // Existing implementations seem to do the same thing here.
                    end_head: 0xFF,
                    end_sector: 0xFF,
                    end_track: 0xFF,
                    //
                    start_lba: 0x01,
                    size_lba: if last_lba > u32::max_value() as u64 {
                        u32::max_value()
                    } else {
                        last_lba as u32
                    },
                },
                MbrPart::default(),
                MbrPart::default(),
                MbrPart::default(),
            ],
            signature: [0u8; 2],
        }
    }

    /// Create a `ProtectiveMbr` from a `Read`er.
    ///
    /// ## Errors
    ///
    /// - If the `Read`er errors.
    /// - If the MBR is invalid.
    ///
    /// ## Details
    ///
    /// On success, this will have read exactly `block_size` bytes from the `Read`er.
    ///
    /// On error, the amount read is unspecified.
    pub(crate) fn from_reader<R: Read + Seek>(mut source: R, block_size: u64) -> Result<Self> {
        let obj: Self = bincode::deserialize_from(&mut source).context(Parse)?;
        obj.validate()?;
        // Seek past the remaining block.
        source
            .seek(SeekFrom::Current(block_size as i64 - 512))
            .context(Io)?;
        Ok(obj)
    }

    /// Write a GPT Protective MBR to a `Write`er.
    ///
    /// ## Errors
    ///
    /// ## Details
    ///
    /// On success, this will have written exactly `block_size` bytes.
    ///
    /// On error, the amount written is unspecified.
    pub(crate) fn to_writer<W: Write + Seek>(&self, mut dest: W, block_size: u64) -> Result<()> {
        bincode::serialize_into(&mut dest, self).context(Parse)?;
        // Account for reserved space.
        let len = (block_size - 512) as usize;
        dest.write_all(&vec![0; len]).context(Io)?;
        Ok(())
    }

    /// Validate the Protective MBR.
    ///
    /// ## Details
    ///
    /// - Ensures the signature is correct.
    /// - Ensures there are no other partitions.
    fn validate(&self) -> Result<()> {
        ensure!(
            self.signature[0] == 0x55 && self.signature[1] == 0xAA,
            Signature {
                signature: self.signature
            }
        );
        for part in &self.partitions[1..] {
            ensure!(*part == MbrPart::default(), Validation);
        }
        Ok(())
    }
}

impl std::fmt::Debug for ProtectiveMbr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("ProtectiveMbr")
            .field("partition", &self.partitions[0])
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

    /// Size of the disk, in LBA, minus one.
    size_lba: u32,
}
