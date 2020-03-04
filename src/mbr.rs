//! MBR definitions
use crate::types::*;
use core::{convert::TryFrom, mem::size_of};
use displaydoc::Display;
use generic_array::{typenum::U440, GenericArray};
#[cfg(any(feature = "std", test))]
use thiserror::Error;

#[derive(Debug, Display)]
#[cfg_attr(any(feature = "std", test), derive(Error))]
pub enum Error {
    /// The MBR was invalid: {0}
    InvalidMbr(&'static str),

    /// Not a GUID Partition Table, MBR has real partitions.
    NotGpt,
}

type Result<T, E = Error> = core::result::Result<T, E>;

pub const MBR_SIZE: usize = 512;

/// GPT Protective MBR
#[derive(PartialEq, Copy, Clone)]
#[repr(C, packed)]
pub struct ProtectiveMbr {
    /// Bios boot code. Unused by GPT.
    boot_code: GenericArray<u8, U440>,

    /// A unique signature. Unused by GPT.
    /// Hard-coded to 0.
    unique_signature: [u8; 4],

    /// Hard-coded to 0.
    unknown: [u8; 2],

    /// Hard-coded to one partition, covering the entire device.
    partitions: [MbrPart; 4],

    /// Hard-coded to 0xAA55-LE.
    signature: u16,
}

// Crate public
impl ProtectiveMbr {
    /// Creates a new Protective MBR
    ///
    /// `last_lba`, the last usable logical block address on the device.
    pub fn new(last_lba: LogicalBlockAddress) -> Self {
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
                    // Technically incorrect?, but
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
            signature: 0xAA55,
        }
    }

    /// Read a `ProtectiveMbr` from a byte slice.
    ///
    /// # Errors
    ///
    /// - If the MBR is invalid
    ///
    /// # Panics
    ///
    /// - If `source` is not [`MBR_SIZE`] bytes.
    pub fn from_bytes(source: &[u8]) -> Result<Self> {
        assert_eq!(source.len(), MBR_SIZE, "Invalid source");
        // Safe because ProtectiveMbr is simple and repr(C, packed),
        // any value is valid, and we check the size of `source` above.
        let mbr = unsafe { (source.as_ptr() as *const ProtectiveMbr).read_unaligned() };
        let mbr = mbr.validate()?;
        Ok(mbr)
    }

    /// Write a GPT Protective MBR to `dest`
    ///
    /// # Panics
    ///
    /// - If `dest` is not [`MBR_SIZE`] bytes
    pub fn to_bytes(&self, dest: &mut [u8]) {
        assert_eq!(dest.len(), MBR_SIZE, "Invalid dest");
        let raw = self as *const ProtectiveMbr as *const u8;
        // Safe because we know the sizes
        let raw = unsafe { core::slice::from_raw_parts(raw, size_of::<ProtectiveMbr>()) };
        dest.copy_from_slice(raw);
    }
}

// Private
impl ProtectiveMbr {
    /// Validate the Protective MBR.
    ///
    /// # Errors
    ///
    /// The MBR is considered invalid if any of the following are true:
    ///
    /// - The signature is not correct
    /// - The GPT Protective partition is missing
    /// - If other partitions exist. In this case the error is [`Error::NotGpt`]
    fn validate(self) -> Result<Self> {
        if self.signature != 0xAA55 {
            return Err(Error::InvalidMbr("MBR signature invalid. Expected 0xAA55"));
        }
        let part: MbrPart = self.partitions[0];
        if part.os_type != 0xEE {
            return Err(Error::InvalidMbr("Missing GPT Protective Partition"));
        }

        let parts = self.partitions;
        for part in &parts[1..] {
            if *part != MbrPart::default() {
                return Err(Error::NotGpt);
            }
        }
        Ok(self)
    }
}

/// Smaller Debug output.
impl core::fmt::Debug for ProtectiveMbr {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("ProtectiveMbr")
            .field("partition 0", &{ self.partitions[0] })
            .finish()
    }
}

#[derive(Debug, Default, PartialEq, Copy, Clone)]
#[repr(C)]
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
    use crate::util::{Result, *};
    use static_assertions::*;

    assert_eq_size!(MbrPart, [u8; 16]);
    assert_eq_size!(ProtectiveMbr, [u8; MBR_SIZE]);

    /// Basic reading should work and validate correctly.
    #[test]
    fn read_test() -> Result {
        let data = data()?;
        let _mbr = ProtectiveMbr::from_bytes(&data[..MBR_SIZE])?;
        Ok(())
    }
}
