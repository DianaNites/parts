//! MBR definitions
use snafu::IntoError;
use snafu::NoneError;
use snafu::{ensure, ResultExt, Snafu};
use std::convert::TryInto;
use std::io::prelude::*;

// TODO: Should be user-defined
const SECTOR_BYTE_SIZE: usize = 512;

#[derive(Debug, Snafu)]
pub struct MbrError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid Protective/Legacy MBR: {}", source))]
    InvalidMbr { source: std::io::Error },

    #[snafu(display("Invalid MBR Signature"))]
    InvalidMbrSig {},

    #[snafu(display("Invalid MBR Partition"))]
    InvalidMbrPartition {},
}

type Result<T, E = MbrError> = std::result::Result<T, E>;

/// Protective MBR
pub struct ProtectiveMbr {
    boot_code: [u8; 440],
    unique_signature: [u8; 4],
    unknown: [u8; 2],
    partitions: [u8; 16 * 4],
    signature: [u8; 2],
    // Technically exists, but we can ignore it.
    // reserved: [u8; LBA - 512],
}

impl ProtectiveMbr {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a `ProtectiveMbr` from a `Read`er.
    ///
    /// # Errors
    ///
    /// - If the `Read`er errors.
    /// - If the MBR is superficially invalid. Not extensively validated.
    ///
    /// The position of the `Read`er is undefined on error.
    pub fn from_reader<R: Read>(mut source: R) -> Result<Self> {
        let mut buf = [0u8; SECTOR_BYTE_SIZE];
        source.read_exact(&mut buf).context(InvalidMbr)?;
        //
        Self::from_bytes(&buf)
    }

    /// Create a `ProtectiveMbr` from bytes.
    ///
    /// See `Self::from_reader` for error details.
    pub fn from_bytes(source: &[u8]) -> Result<Self> {
        let mut mbr = Self::new();
        //
        mbr.boot_code.copy_from_slice(&source[0..440]);
        mbr.unique_signature.copy_from_slice(&source[440..444]);
        mbr.unknown.copy_from_slice(&source[444..446]);
        // TODO: Properly read partitions?
        mbr.partitions.copy_from_slice(&source[446..446 + (16 * 4)]);
        //
        mbr.signature.copy_from_slice(&source[510..512]);
        //
        if mbr.signature[0] != 0x55 || mbr.signature[1] != 0xAA {
            return InvalidMbrSig.fail().map_err(|e| e.into());
        }
        Ok(mbr)
    }
}

impl std::fmt::Debug for ProtectiveMbr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.boot_code[..].fmt(f)?;
        self.unique_signature[..].fmt(f)?;
        self.unknown[..].fmt(f)?;
        self.partitions[..].fmt(f)?;
        self.signature[..].fmt(f)?;
        Ok(())
    }
}

impl Default for ProtectiveMbr {
    fn default() -> Self {
        Self {
            boot_code: [0u8; 440],
            unique_signature: [0u8; 4],
            unknown: [0u8; 2],
            partitions: [0u8; 16 * 4],
            signature: [0u8; 2],
        }
    }
}

#[derive(Debug, Default)]
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

impl MbrPart {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_reader<R: Read>(mut source: R) -> Result<Self> {
        // MBR Partitions are 16 bytes.
        let mut buf = [0u8; 16];
        source.read_exact(&mut buf).context(InvalidMbr)?;
        Self::from_bytes(&buf)
    }

    pub fn from_bytes(source: &[u8]) -> Result<Self> {
        if source.len() < 16 {
            return InvalidMbrPartition.fail().map_err(|e| e.into());
        }
        //
        let mut part = Self::new();
        // Boot flag
        part.boot = source[0];
        // CHS Start
        part.start_head = source[1];
        part.start_sector = source[2];
        part.start_track = source[3];
        // OS Type
        part.os_type = source[4];
        // CHS End
        part.end_head = source[5];
        part.end_sector = source[6];
        part.end_track = source[7];
        // LBA
        part.start_lba = u32::from_le_bytes(source[8..=11].try_into().unwrap());
        part.size_lba = u32::from_le_bytes(source[12..=16].try_into().unwrap());
        //
        Ok(part)
    }
}
