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

    #[snafu(display("Error parsing MBR Header structure"))]
    Parse { source: bincode::Error },

    #[snafu(display("Error reading from device"))]
    Io { source: std::io::Error },
}

type Result<T, E = MbrError> = std::result::Result<T, E>;

/// GPT Protective MBR
#[derive(Default, Serialize, Deserialize)]
pub struct ProtectiveMbr {
    #[serde(with = "mbr_boot_code")]
    boot_code: Vec<u8>,

    unique_signature: [u8; 4],
    unknown: [u8; 2],
    partitions: [MbrPart; 4],
    signature: [u8; 2],
}

impl ProtectiveMbr {
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

    fn validate(&self) -> Result<(), InnerError> {
        ensure!(
            self.signature[0] == 0x55 && self.signature[1] == 0xAA,
            Signature
        );
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

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct MbrPart {
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
