//! Test utility stuff
use crate::types::*;
use std::{fs, io::prelude::*};

/// Path to cfdisk test data
pub static TEST_PARTS_CF: &str = "tests/data/test_parts_cf";

/// Test data block size
pub const BLOCK_SIZE: BlockSize = BlockSize(512);

/// Byte size of test data
pub const TEN_MIB_BYTES: usize = 10_485_760;

/// Expected Disk UUID
pub const CF_DISK_GUID: &str = "A17875FB-1D86-EE4D-8DFE-E3E8ABBCD364";

/// Expected Partition UUID
pub const CF_PART_GUID: &str = "97954376-2BB6-534B-A015-DF434A94ABA2";

/// Result type. Note that this must be imported explicitly or else it's
/// ambiguous with std prelude
pub type Result<T = ()> = anyhow::Result<T>;

/// Read test data
pub fn data() -> Result<Vec<u8>> {
    let mut data = vec![0; TEN_MIB_BYTES];
    let mut file = fs::File::open(TEST_PARTS_CF)?;
    file.read_exact(&mut data)?;
    Ok(data)
}
