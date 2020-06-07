//! Type-safe Newtype wrappers
use core::{num::NonZeroU64, ops};
use derive_more::*;
#[cfg(feature = "serde")]
use serde_crate::{Deserialize, Serialize};

/// Helper to define ByteSize from_* setters.
macro_rules! __ByteSizeImplFrom {
    // FIXME: Remove when const-int-pow is stable.
    ("Bytes", $p:ident, $v:expr) => {
        /// Create a [`Size`] from the specified number of `Bytes`
        pub const fn $p($p: u64) -> Self {
            Self($p)
        }
    };

    ($m:expr, $p:ident, $v:expr) => {
        /// Create a [`Size`] from the specified number of `
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
        // FIXME: Use below when const-int-pow stable
        // __ByteSizeImplAs!(
        //     /// Return the number of `Bytes` contained by this [`Size`].
        //     @func $p ,$v
        // );
        /// Return the number of `Bytes` contained by this [`Size`].
        pub const fn $p(&self) -> u64 {
            self.0
        }
    };
    ($m:expr, $p:ident, $v:expr) => {
        __ByteSizeImplAs!(
            /// Return the number of *whole* `
            #[doc = $m]
            ///` contained by this [`Size`].
            @func $p, $v
        );
    };
}

/// GPT Block Size, in bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into, Display)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(crate = "serde_crate", transparent)
)]
#[repr(transparent)]
pub struct BlockSize(NonZeroU64);

impl BlockSize {
    /// Create a new `BlockSize`.
    ///
    /// # Panics
    ///
    /// - If `val` is zero.
    pub fn new(val: u64) -> Self {
        Self(NonZeroU64::new(val).unwrap())
    }

    /// Create a new `BlockSize`.
    ///
    /// # Safety
    ///
    /// - `val` must not be zero.
    pub const unsafe fn new_unchecked(val: u64) -> Self {
        Self(NonZeroU64::new_unchecked(val))
    }

    /// Get the block size as a `u64`
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

/// Represents a byte offset.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default, Display, Into, From)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(crate = "serde_crate", transparent)
)]
#[repr(transparent)]
pub struct Offset(pub u64);

/// The Logical [`Block`] representing this [`Offset`]
impl ops::Div<BlockSize> for Offset {
    type Output = Block;

    fn div(self, rhs: BlockSize) -> Self::Output {
        let block = self.0 / rhs.get();
        Block(block)
    }
}

impl From<Size> for Offset {
    fn from(s: Size) -> Self {
        Offset(s.as_bytes())
    }
}

/// Device or Partition Size.
#[derive(
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Debug,
    Default,
    Display,
    Into,
    From,
    Add,
    Sub,
    Mul,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
)]
#[display(fmt = "{} Bytes", _0)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(crate = "serde_crate", transparent)
)]
#[repr(transparent)]
pub struct Size(u64);

impl Size {
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

/// A [`Size`] from an [`Offset`]
impl From<Offset> for Size {
    fn from(o: Offset) -> Self {
        Self(o.0)
    }
}

/// A [`Size`] from a [`BlockSize`]
impl From<BlockSize> for Size {
    fn from(o: BlockSize) -> Self {
        Self(o.get())
    }
}

impl ops::Add<BlockSize> for Size {
    type Output = Size;

    fn add(self, rhs: BlockSize) -> Self::Output {
        self + Size(rhs.get())
    }
}

impl ops::AddAssign<BlockSize> for Size {
    fn add_assign(&mut self, rhs: BlockSize) {
        *self += Size(rhs.get());
    }
}

impl ops::Sub<BlockSize> for Size {
    type Output = Size;

    fn sub(self, rhs: BlockSize) -> Self::Output {
        self - Size(rhs.get())
    }
}

impl ops::SubAssign<BlockSize> for Size {
    fn sub_assign(&mut self, rhs: BlockSize) {
        *self -= Size(rhs.get());
    }
}

/// The last Logical Block (inclusive)
impl ops::Div<BlockSize> for Size {
    type Output = Block;

    fn div(self, rhs: BlockSize) -> Self::Output {
        let block = self.0 / rhs.get();
        Block(block)
    }
}

/// Device Logical Block Address
///
/// The size of a block is dependent on it's associated [`BlockSize`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Display, Default)]
#[cfg_attr(
    feature = "serde",
    derive(Serialize, Deserialize),
    serde(crate = "serde_crate", transparent)
)]
#[display(fmt = "Block {}", _0)]
#[repr(transparent)]
pub struct Block(pub u64);

impl ops::Mul<BlockSize> for Block {
    type Output = Offset;

    fn mul(self, rhs: BlockSize) -> Self::Output {
        Offset(self.0 * rhs.get())
    }
}

impl ops::Add<u64> for Block {
    type Output = Block;

    fn add(self, rhs: u64) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl ops::AddAssign<u64> for Block {
    fn add_assign(&mut self, rhs: u64) {
        self.0 += rhs;
    }
}

impl ops::Sub<u64> for Block {
    type Output = Block;

    fn sub(self, rhs: u64) -> Self::Output {
        Self(self.0 - rhs)
    }
}

impl ops::SubAssign<u64> for Block {
    fn sub_assign(&mut self, rhs: u64) {
        self.0 -= rhs;
    }
}
