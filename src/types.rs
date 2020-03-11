//! Types for use in [`crate::Gpt`]
use core::ops;
use derive_more::*;

/// Helper to define ByteSize from_* setters.
macro_rules! __ByteSizeImplFrom {
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
        __ByteSizeImplAs!(
            /// Return the number of `Bytes` contained by this [`Size`].
            @func $p ,$v
        );
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

/// Represents a devices Block Size, in bytes.
///
/// This is usually either `512` or `4096`, but can be any value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into, Display)]
#[repr(transparent)]
pub struct BlockSize(pub u64);

/// Represents a byte offset
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default, Display, Into, From)]
#[repr(transparent)]
pub struct Offset(pub u64);

/// The Logical [`Block`] representing this [`Offset`]
impl ops::Div<BlockSize> for Offset {
    type Output = Block;

    fn div(self, rhs: BlockSize) -> Self::Output {
        let block = self.0 / rhs.0;
        Block::new(block, rhs)
    }
}

impl From<Size> for Offset {
    fn from(s: Size) -> Self {
        Offset(s.as_bytes())
    }
}

/// Represents a size
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
        Self(o.0)
    }
}

impl ops::Add<BlockSize> for Size {
    type Output = Size;

    fn add(self, rhs: BlockSize) -> Self::Output {
        self + Size(rhs.0)
    }
}

impl ops::AddAssign<BlockSize> for Size {
    fn add_assign(&mut self, rhs: BlockSize) {
        *self += Size(rhs.0);
    }
}

impl ops::Sub<BlockSize> for Size {
    type Output = Size;

    fn sub(self, rhs: BlockSize) -> Self::Output {
        self - Size(rhs.0)
    }
}

impl ops::SubAssign<BlockSize> for Size {
    fn sub_assign(&mut self, rhs: BlockSize) {
        *self -= Size(rhs.0);
    }
}

/// The last Logical Block (inclusive)
impl ops::Div<BlockSize> for Size {
    type Output = Block;

    fn div(self, rhs: BlockSize) -> Self::Output {
        let block = self.0 / rhs.0;
        Block::new(block, rhs)
    }
}

/// Represents a Logical Block Address
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Display)]
#[display(fmt = "Block {}", block)]
pub struct Block {
    block: u64,
    size: BlockSize,
}

impl Block {
    /// Create a new Block
    pub fn new(block: u64, block_size: BlockSize) -> Self {
        Self {
            block,
            size: block_size,
        }
    }

    /// Get the [`Offset`] representing this Block
    pub fn into_offset(self) -> Offset {
        Offset(self.block * self.size.0)
    }
}

impl ops::Add<u64> for Block {
    type Output = Block;

    fn add(self, rhs: u64) -> Self::Output {
        Self {
            block: self.block + rhs,
            size: self.size,
        }
    }
}

impl ops::AddAssign<u64> for Block {
    fn add_assign(&mut self, rhs: u64) {
        self.block += rhs;
    }
}

impl ops::Sub<u64> for Block {
    type Output = Block;

    fn sub(self, rhs: u64) -> Self::Output {
        Self {
            block: self.block - rhs,
            size: self.size,
        }
    }
}

impl ops::SubAssign<u64> for Block {
    fn sub_assign(&mut self, rhs: u64) {
        self.block -= rhs;
    }
}

/// The logical block
impl From<Block> for u64 {
    fn from(b: Block) -> Self {
        b.block
    }
}
