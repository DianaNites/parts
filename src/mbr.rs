//! MBR definitions
use snafu::{ResultExt, Snafu};
use std::io::prelude::*;

// TODO: Should be user-defined
const SECTOR_BYTE_SIZE: usize = 512;

#[derive(Debug, Snafu)]
pub struct MbrError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid Protective/Legacy MBR: {}", source))]
    InvalidMbr { source: std::io::Error },
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

    pub fn from_reader<RS: Read + Seek>(mut source: RS) -> Result<Self> {
        let mut mbr = Self::new();
        //
        let mut buf = [0u8; SECTOR_BYTE_SIZE];
        source.read_exact(&mut buf).context(InvalidMbr)?;
        //
        mbr.boot_code.copy_from_slice(&buf[0..440]);
        mbr.unique_signature.copy_from_slice(&buf[440..444]);
        mbr.unknown.copy_from_slice(&buf[444..446]);
        unimplemented!()
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
