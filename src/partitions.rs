//! Known partition types
use derive_more::Display;
#[cfg(feature = "serde")]
use serde_crate::{Deserialize, Serialize};
use uuid::Uuid;

/// Define a partition type
macro_rules! partition_type {
    ($(
        #[$($meta:meta)*]
        $name:ident($uuid:literal)
    ),+ $(,)?) => {
        /// Recognized GPT Partition Types.
        ///
        /// This enum is `non_exhaustive`, be prepared for matches to change.
        ///
        /// In particular, [`PartitionType::Unknown`] is likely to change,
        /// as more partition types become recognized.
        #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
        #[cfg_attr(
            feature = "serde",
            derive(Serialize, Deserialize),
            serde(crate = "serde_crate")
        )]
        #[non_exhaustive]
        pub enum PartitionType {
            /// The partition type is unknown.
            Unknown(Uuid),

            $(
                #[$($meta)*]
                $name
            ),+
        }

        impl PartitionType {
            /// Get [`Uuid`] from PartitionType
            pub fn to_uuid(self) -> Uuid {
                match self {
                    $(
                        Self::$name => Uuid::parse_str($uuid).expect("BUG: Partition type defined incorrectly"),
                    )+
                    Self::Unknown(u) => u,
                }
            }

            /// Get PartitionType from [`Uuid`]
            ///
            /// # Panics
            ///
            /// - If `uuid` can't be parsed
            pub fn from_uuid(uuid: Uuid) -> Self {
                let mut buf = Uuid::encode_buffer();
                let s = uuid.to_hyphenated().encode_upper(&mut buf);
                match &*s {
                    $(
                        $uuid => Self::$name,
                    )*
                    u => Self::Unknown(Uuid::parse_str(u).expect("BUG: Couldn't parse UUID")),
                }
            }
        }

        impl Default for PartitionType {
            fn default() -> Self {
                // INFO: This is kinda hacky, it depends on `Unused` being defined
                Self::Unused
            }
        }
    };
}

partition_type! {
    /// Unused entry
    Unused("00000000-0000-0000-0000-000000000000"),

    /// Partition contains legacy MBR
    LegacyMbr("024DEE41-33E7-11D3-9D69-0008C781F39F"),

    /// EFI System Partition
    EfiSystem("C12A7328-F81F-11D2-BA4B-00A0C93EC93B"),

    /// Microsoft Reserved Partition
    MicrosoftReserved("E3C9E316-0B5C-4DB8-817D-F92DF00215AE"),

    /// Microsoft Basic Data
    MicrosoftBasicData("EBD0A0A2-B9E5-4433-87C0-68B6B72699C7"),

    /// Microsoft Recovery Tools Environment
    MicrosoftRecoveryEnvironment("DE94BBA4-06D1-4D40-A16A-BFD50179D6AC"),

    /// Microsoft Logical Disk Manager Metadata
    MicrosoftLdmMetadata("5808C8AA-7E8F-42E0-85D2-E1E90434CFB3"),

    /// Microsoft Logical Disk Manager Data Partition
    MicrosoftLdm("AF9B60A0-1431-4F62-BC68-3311714A69AD"),

    /// Microsoft Storage Spaces
    MicrosoftStorageSpace("E75CAF8F-F680-4CEE-AFA3-B001E56EFC2D"),

    /// Linux Filesystem
    LinuxFilesystemData("0FC63DAF-8483-4772-8E79-3D69D8477DE4"),

    /// Linux Swap
    LinuxSwap("0657FD6D-A4AB-43C4-84E5-0933C84B4F4F"),

    /// Linux Logical Volume Management
    LinuxLvm("E6D6D379-F507-44C2-A23C-238F2A3DF928"),

    /// Linux Reserved
    LinuxReserved("8DA63339-0007-60C0-C436-083AC8230908"),

    /// CoreOS Alias for historical `coreos-rootfs`
    CoreOsUsr("5DFBF5F4-2848-4BAC-AA5E-0D9A20B745A6"),

    /// CoreOS Auto-resizing
    CoreOsResize("3884DD41-8582-4404-B9A8-E9B84F2DF50E"),

    /// CoreOS Reserved for OEM usage
    CoreOsReserved("C95DC21A-DF0E-4340-8D7B-26CBFA9A03E0"),

    /// CoreOS RAID partition containing a rootfs
    CoreOsRootRaid("BE9067B9-EA49-4F15-B4F6-F36F8C9E1818"),
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
