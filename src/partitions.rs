//! Known partition types
use uuid::Uuid;

/// Recognized GPT Partition Types
///
/// This is non-exhaustive,
/// it's unrecommended to match on this.
///
/// Types that match against the [`PartitionType::Unknown`] variant
/// are not guaranteed to continue to do so, as more partition types
/// become recognized.
#[derive(Debug, Copy, Clone)]
pub enum PartitionType {
    /// Unused entry
    Unused,

    /// The partition type is unknown.
    Unknown,

    /// Partition contains legacy MBR
    LegacyMbr,

    /// EFI System Partition
    EfiSystem,

    /// Microsoft Reserved Partition
    MicrosoftReserved,

    /// Microsoft Basic Data
    MicrosoftBasicData,

    /// Linux Filesystem
    LinuxFilesystemData,

    /// Linux Swap
    LinuxSwap,
}

mod types {
    pub const UNUSED: &str = "00000000-0000-0000-0000-000000000000";
    pub const MBR: &str = "024DEE41-33E7-11D3-9D69-0008C781F39F";
    pub const EFI: &str = "C12A7328-F81F-11D2-BA4B-00A0C93EC93B";
    pub const MS_RESERVED: &str = "E3C9E316-0B5C-4DB8-817D-F92DF00215AE";
    pub const MS_BASIC: &str = "EBD0A0A2-B9E5-4433-87C0-68B6B72699C7";
    pub const LINUX_DATA: &str = "0FC63DAF-8483-4772-8E79-3D69D8477DE4";
    pub const LINUX_SWAP: &str = "0657FD6D-A4AB-43C4-84E5-0933C84B4F4F";
}
use types::*;

impl PartitionType {
    pub(crate) fn to_uuid(&self) -> Uuid {
        match self {
            PartitionType::Unused => Uuid::nil(),
            PartitionType::Unknown => Uuid::nil(),
            PartitionType::LegacyMbr => Uuid::parse_str(MBR).unwrap(),
            PartitionType::EfiSystem => Uuid::parse_str(EFI).unwrap(),
            PartitionType::MicrosoftReserved => Uuid::parse_str(MS_RESERVED).unwrap(),
            PartitionType::MicrosoftBasicData => Uuid::parse_str(MS_BASIC).unwrap(),
            PartitionType::LinuxFilesystemData => Uuid::parse_str(LINUX_DATA).unwrap(),
            PartitionType::LinuxSwap => Uuid::parse_str(LINUX_SWAP).unwrap(),
        }
    }

    pub(crate) fn from_uuid(uuid: Uuid) -> Self {
        let mut buf = Uuid::encode_buffer();
        let s = uuid.to_hyphenated().encode_upper(&mut buf);
        match &*s {
            UNUSED => PartitionType::Unused,
            MBR => PartitionType::LegacyMbr,
            EFI => PartitionType::EfiSystem,
            MS_RESERVED => PartitionType::MicrosoftReserved,
            MS_BASIC => PartitionType::MicrosoftBasicData,
            LINUX_DATA => PartitionType::LinuxFilesystemData,
            LINUX_SWAP => PartitionType::LinuxSwap,
            _ => PartitionType::Unknown,
        }
    }
}
