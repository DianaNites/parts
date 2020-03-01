//! Types for use in [`crate::Gpt`]
use derive_more::*;

/// Helper to define ByteSize from_* setters.
macro_rules! __ByteSizeImplFrom {
    ($m:expr, $p:ident, $v:expr) => {
        /// Create a [`ByteSize`] from the specified number of `
        #[doc = $m]
        ///`
        pub fn $p($p: u64) -> Self {
            Self($p * 1024u64.pow($v))
        }
    };
}

/// Helper to define ByteSize as_* getters.
macro_rules! __ByteSizeImplAs {
    (
        $(#[$outer:meta])*
        @func $p:ident, $v:expr
    ) => {
        $(#[$outer])*
        pub fn $p(&self) -> u64 {
            self.0 / 1024u64.pow($v)
        }
    };
    ("Bytes", $p:ident, $v:expr) => {
        __ByteSizeImplAs!(
            /// Return the number of `Bytes` contained by this [`ByteSize`].
            @func $p ,$v
        );
    };
    ($m:expr, $p:ident, $v:expr) => {
        __ByteSizeImplAs!(
            /// Return the number of *whole* `
            #[doc = $m]
            ///` contained by this [`ByteSize`].
            @func $p, $v
        );
    };
}

/// Represents a devices Block Size, in bytes.
///
/// This is usually either `512` or `4096`, but can be any value.
///
/// This type always has the same representation as a [`u64`]
///
/// # Examples
///
/// Some basic math
///
/// ```rust
/// # use parts::types::*;
/// let block = BlockSize(512);
/// assert_eq!(block * 2, BlockSize(1024));
/// assert_eq!(block / 2, BlockSize(256));
/// ```
///
/// This doesn't compile, adding or subtracting
/// arbitrary numbers from a BlockSize isn't valid.
///
/// ```rust,compile_fail
/// # use parts::types::*;
/// let block = BlockSize(512);
/// // Doesn't compile, adding/subtracting
/// // arbitrary numbers from blocks isn't valid.
/// assert_eq!(block + 2, 514);
/// assert_eq!(block - 2, 510);
/// ```
#[derive(
    Debug,
    Display,
    From,
    Add,
    Sub,
    Mul,
    Div,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Default,
)]
#[repr(transparent)]
pub struct BlockSize(pub u64);

/// A `ByteSize` type represents a size, in bytes.
///
/// This type always has the same representation as a [`u64`]
///
/// This type can be constructed from various
/// different Binary/SI units.
///
/// # Example
///
/// ```rust
/// # use parts::types::ByteSize;
/// let mib = ByteSize::from_mib(1);
///
/// println!("Mebibytes: {}", mib.as_mib());
/// println!("Bytes: {}", mib.as_bytes());
/// println!("ByteSize: {}", mib); // Displays as bytes.
/// ```
#[derive(
    Debug,
    Display,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Default,
)]
#[display(fmt = "{} Bytes", _0)]
#[repr(transparent)]
pub struct ByteSize(u64);

impl ByteSize {
    __ByteSizeImplFrom!("Bytes", from_bytes, 0);
    __ByteSizeImplFrom!("KiB", from_kib, 1);
    __ByteSizeImplFrom!("MiB", from_mib, 2);
    __ByteSizeImplFrom!("GiB", from_gib, 3);
    __ByteSizeImplFrom!("TiB", from_tib, 4);
    __ByteSizeImplFrom!("PiB", from_pib, 5);
    //
    __ByteSizeImplAs!("Bytes", as_bytes, 0);
    __ByteSizeImplAs!("KiB", as_kib, 1);
    __ByteSizeImplAs!("MiB", as_mib, 2);
    __ByteSizeImplAs!("GiB", as_gib, 3);
    __ByteSizeImplAs!("TiB", as_tib, 4);
    __ByteSizeImplAs!("PiB", as_pib, 5);
}

/// Represents a Logical Block Address.
///
/// This is used by GPT/EFI to locate areas on a device.
/// Addressing is in blocks of [`BlockSize`].
/// This is the smallest unit a GPT label can address.
///
/// This type always has the same representation as a [`u64`]
///
/// # Examples
///
/// Calculate the last Logical Block Address
///
/// ```rust
/// # use parts::types::*;
/// let disk_size = ByteSize::from_mib(10);
/// let block_size = BlockSize(512);
///
/// let last_lba = disk_size / block_size;
/// println!("The last Logical Block Address is: {}", last_lba);
/// ```
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Display,
    From,
    Add,
    Sub,
    Mul,
    AddAssign,
    SubAssign,
    MulAssign,
    Hash,
    Default,
)]
#[repr(transparent)]
pub struct LogicalBlockAddress(pub u64);

/// Add a [`u64`] to a [`LogicalBlockAddress`],
/// returning a [`LogicalBlockAddress`].
impl core::ops::Add<u64> for LogicalBlockAddress {
    type Output = Self;

    fn add(self, other: u64) -> Self {
        Self(self.0 + other)
    }
}

/// Subtract a [`u64`] from a [`LogicalBlockAddress`],
/// returning a [`LogicalBlockAddress`].
impl core::ops::Sub<u64> for LogicalBlockAddress {
    type Output = Self;

    fn sub(self, other: u64) -> Self {
        Self(self.0 - other)
    }
}

/// Multiplying a [`LogicalBlockAddress`] by a [`BlockSize`]
/// gives the byte offset of the [`LogicalBlockAddress`], in [`ByteSize`]
impl core::ops::Mul<BlockSize> for LogicalBlockAddress {
    type Output = ByteSize;

    fn mul(self, other: BlockSize) -> ByteSize {
        ByteSize::from_bytes((self * other.0).0)
    }
}

/// Dividing a [`ByteSize`] by a [`BlockSize`]
/// returns a [`LogicalBlockAddress`].
impl core::ops::Div<BlockSize> for ByteSize {
    type Output = LogicalBlockAddress;

    fn div(self, other: BlockSize) -> LogicalBlockAddress {
        LogicalBlockAddress((self / other.0).as_bytes())
    }
}

/// A [`ByteSize`] can be constructed from a [`BlockSize`],
/// which is always some value in bytes.
impl From<BlockSize> for ByteSize {
    fn from(b: BlockSize) -> Self {
        ByteSize::from_bytes(b.0)
    }
}
