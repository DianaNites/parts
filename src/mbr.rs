//! MBR definitions
use crate::util::*;
use serde::{Deserialize, Serialize};
use snafu::{ensure, ResultExt, Snafu};
use std::io::{prelude::*, SeekFrom};

#[derive(Debug, Snafu)]
pub struct MbrError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid MBR Signature"))]
    Signature {},

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
    #[serde(with = "mbr_boot_code")]
    boot_code: Vec<u8>,

    unique_signature: [u8; 4],
    unknown: [u8; 2],
    partitions: [MbrPart; 4],
    signature: [u8; 2],
}

impl ProtectiveMbr {
    /// Creates a new Protective MBR
    pub(crate) fn new(last_lba: u64) -> Self {
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
    /// # Errors
    ///
    /// - If the `Read`er errors.
    /// - If the MBR is invalid.
    ///
    /// The position of the `Read`er is undefined on error.
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
    pub(crate) fn to_writer<W: Write + Seek>(&self, mut dest: W, block_size: u64) -> Result<()> {
        bincode::serialize_into(&mut dest, self).context(Parse)?;
        // Account for reserved space.
        let len = (block_size - 512) as usize;
        dest.write_all(&vec![0; len]).context(Io)?;
        Ok(())
    }

    fn validate(&self) -> Result<(), InnerError> {
        ensure!(
            self.signature[0] == 0x55 && self.signature[1] == 0xAA,
            Signature
        );
        for part in &self.partitions {
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
    boot: u8,
    // CHS
    start_head: u8,
    start_sector: u8,
    start_track: u8,
    //
    os_type: u8,
    // CHS
    end_head: u8,
    end_sector: u8,
    end_track: u8,
    //
    start_lba: u32,
    size_lba: u32,
}
