//! Known partition types
use derive_more::Display;
use uuid::Uuid;

/// Recognized GPT Partition Types
///
/// A UUID that matches against the [`PartitionType::Unknown`] variant
/// is not guaranteed to continue to do so, as more partition types
/// become recognized.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[non_exhaustive]
pub enum PartitionType {
    /// Unused entry
    Unused,

    /// The partition type is unknown.
    Unknown(Uuid),

    /// Partition contains legacy MBR
    LegacyMbr,

    /// EFI System Partition
    EfiSystem,

    /// Microsoft Reserved Partition
    MicrosoftReserved,

    /// Microsoft Basic Data
    MicrosoftBasicData,

    /// Microsoft Recovery Tools Environment
    MicrosoftRecoveryEnvironment,

    /// Microsoft Logical Disk Manager Metadata
    MicrosoftLdmMetadata,

    /// Microsoft Logical Disk Manager Data Partition
    MicrosoftLdm,

    /// Microsoft Storage Spaces
    MicrosoftStorageSpace,

    /// Linux Filesystem
    LinuxFilesystemData,

    /// Linux Swap
    LinuxSwap,

    /// Linux Reserved
    LinuxReserved,

    /// Linux Logical Volume Management
    LinuxLvm,

    /// CoreOS Alias for historical `coreos-rootfs`
    CoreOsUsr,

    /// CoreOS Auto-resizing
    CoreOsResize,

    /// CoreOS Reserved for OEM usage
    CoreOsReserved,

    /// CoreOS RAID partition containing a rootfs
    CoreOsRootRaid,
}

impl Default for PartitionType {
    fn default() -> Self {
        PartitionType::Unused
    }
}

// Helps macro
mod types {
    #![allow(non_upper_case_globals)]
    pub const Unused: &str = "00000000-0000-0000-0000-000000000000";
    pub const LegacyMbr: &str = "024DEE41-33E7-11D3-9D69-0008C781F39F";
    pub const EfiSystem: &str = "C12A7328-F81F-11D2-BA4B-00A0C93EC93B";
    //
    pub const MicrosoftReserved: &str = "E3C9E316-0B5C-4DB8-817D-F92DF00215AE";
    pub const MicrosoftBasicData: &str = "EBD0A0A2-B9E5-4433-87C0-68B6B72699C7";
    pub const MicrosoftRecoveryEnvironment: &str = "DE94BBA4-06D1-4D40-A16A-BFD50179D6AC";
    pub const MicrosoftLdmMetadata: &str = "5808C8AA-7E8F-42E0-85D2-E1E90434CFB3";
    pub const MicrosoftLdm: &str = "AF9B60A0-1431-4F62-BC68-3311714A69AD";
    pub const MicrosoftStorageSpace: &str = "E75CAF8F-F680-4CEE-AFA3-B001E56EFC2D";
    //
    pub const LinuxFilesystemData: &str = "0FC63DAF-8483-4772-8E79-3D69D8477DE4";
    pub const LinuxSwap: &str = "0657FD6D-A4AB-43C4-84E5-0933C84B4F4F";
    pub const LinuxLvm: &str = "E6D6D379-F507-44C2-A23C-238F2A3DF928";
    pub const LinuxReserved: &str = "8DA63339-0007-60C0-C436-083AC8230908";
    //
    pub const CoreOsUsr: &str = "5dfbf5f4-2848-4bac-aa5e-0d9a20b745a6";
    pub const CoreOsResize: &str = "3884dd41-8582-4404-b9a8-e9b84f2df50e";
    pub const CoreOsReserved: &str = "c95dc21a-df0e-4340-8d7b-26cbfa9a03e0";
    pub const CoreOsRootRaid: &str = "be9067b9-ea49-4f15-b4f6-f36f8c9e1818";
}
use types::*;

macro_rules! __to_uuid_match {
    ($self:ident, $($i:ident),+ $(,)*) => {
        match $self {
            PartitionType::Unused => Uuid::nil(),
            PartitionType::Unknown(u) => u,
            $(
            PartitionType::$i => Uuid::parse_str($i).unwrap(),
            )+
        }
    };
}

macro_rules! __from_uuid_match {
    ($s:ident, $($i:ident),+ $(,)*) => {
        #[allow(non_upper_case_globals)]
        match &*$s {
            Unused => PartitionType::Unused,
            $(
            $i => PartitionType::$i,
            )+
            u => PartitionType::Unknown(Uuid::parse_str(u).unwrap()),
        }
    };
}

impl PartitionType {
    pub(crate) fn to_uuid(self) -> Uuid {
        __to_uuid_match!(
            self,
            LegacyMbr,
            EfiSystem,
            //
            MicrosoftReserved,
            MicrosoftBasicData,
            MicrosoftRecoveryEnvironment,
            MicrosoftLdmMetadata,
            MicrosoftLdm,
            MicrosoftStorageSpace,
            //
            LinuxFilesystemData,
            LinuxSwap,
            LinuxLvm,
            LinuxReserved,
            //
            CoreOsUsr,
            CoreOsResize,
            CoreOsReserved,
            CoreOsRootRaid,
        )
    }

    pub(crate) fn from_uuid(uuid: Uuid) -> Self {
        let mut buf = Uuid::encode_buffer();
        let s = uuid.to_hyphenated().encode_upper(&mut buf);
        __from_uuid_match!(
            s,
            LegacyMbr,
            EfiSystem,
            //
            MicrosoftReserved,
            MicrosoftBasicData,
            MicrosoftRecoveryEnvironment,
            MicrosoftLdmMetadata,
            MicrosoftLdm,
            MicrosoftStorageSpace,
            //
            LinuxFilesystemData,
            LinuxSwap,
            LinuxLvm,
            LinuxReserved,
            //
            CoreOsUsr,
            CoreOsResize,
            CoreOsReserved,
            CoreOsRootRaid,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display() {
        assert_eq!(
            &format!("{}", PartitionType::LinuxFilesystemData),
            "LinuxFilesystemData"
        );
    }
}
