//! Known partition types
use uuid::Uuid;

/// Recognized GPT Partition Types
///
/// This is non-exhaustive,
/// it's unrecommended to match on this.
///
/// A UUID that matches against the [`PartitionType::Unknown`] variant
/// is not guaranteed to continue to do so, as more partition types
/// become recognized.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

// Helps macro
#[allow(non_upper_case_globals)]
mod types {
    pub const Unused: &str = "00000000-0000-0000-0000-000000000000";
    pub const LegacyMbr: &str = "024DEE41-33E7-11D3-9D69-0008C781F39F";
    pub const EfiSystem: &str = "C12A7328-F81F-11D2-BA4B-00A0C93EC93B";
    pub const MicrosoftReserved: &str = "E3C9E316-0B5C-4DB8-817D-F92DF00215AE";
    pub const MicrosoftBasicData: &str = "EBD0A0A2-B9E5-4433-87C0-68B6B72699C7";
    pub const LinuxFilesystemData: &str = "0FC63DAF-8483-4772-8E79-3D69D8477DE4";
    pub const LinuxSwap: &str = "0657FD6D-A4AB-43C4-84E5-0933C84B4F4F";
}
use types::*;

macro_rules! __to_uuid_match {
    ($self:ident, $($i:ident),+) => {
        match $self {
            PartitionType::Unused => Uuid::nil(),
            PartitionType::Unknown => Uuid::nil(),
            $(
            PartitionType::$i => Uuid::parse_str($i).unwrap(),
            )+
        }
    };
}

macro_rules! __from_uuid_match {
    ($s:ident, $($i:ident),+) => {
        #[allow(non_upper_case_globals)]
        match &*$s {
            Unused => PartitionType::Unused,
            $(
            $i => PartitionType::$i,
            )+
            _ => PartitionType::Unknown,
        }
    };
}

impl PartitionType {
    pub(crate) fn to_uuid(&self) -> Uuid {
        __to_uuid_match!(
            self,
            LegacyMbr,
            EfiSystem,
            MicrosoftReserved,
            MicrosoftBasicData,
            LinuxFilesystemData,
            LinuxSwap
        )
    }

    pub(crate) fn from_uuid(uuid: Uuid) -> Self {
        let mut buf = Uuid::encode_buffer();
        let s = uuid.to_hyphenated().encode_upper(&mut buf);
        __from_uuid_match!(
            s,
            LegacyMbr,
            EfiSystem,
            MicrosoftReserved,
            MicrosoftBasicData,
            LinuxFilesystemData,
            LinuxSwap
        )
    }
}
