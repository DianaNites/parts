//! honggfuzz stuff.

#[cfg(fuzzing)]
fn main() {
    use honggfuzz::*;
    use parts::types::*;
    use parts::*;
    use std::{convert::TryInto, io::Cursor};
    const BLOCK_SIZE: BlockSize = BlockSize(512);
    loop {
        fuzz!(|data: &[u8]| {
            let src = Cursor::new(data);
            // Test reading random data doesn't crash.
            if let Ok(s) = Gpt::from_reader(src, BLOCK_SIZE) {
                dbg!(s);
            }
            // If we have enough, pretend to be a disk.
            if data.len() as u64 / BLOCK_SIZE.0 >= 67 {
                let mut new = Gpt::new(BLOCK_SIZE, ByteSize::from_bytes(data.len() as u64));
                if let Ok(s) = std::str::from_utf8(data) {
                    // Random size from the data
                    let (bytes, rest) = data.split_at(std::mem::size_of::<u64>());
                    let size = u64::from_ne_bytes(bytes.try_into().unwrap());
                    // Random start position from the leftover data
                    let (bytes, _) = rest.split_at(std::mem::size_of::<u64>());
                    let start = u64::from_ne_bytes(bytes.try_into().unwrap());
                    //
                    let part = GptPartBuilder::new(BLOCK_SIZE)
                        .name(s)
                        .size(ByteSize::from_bytes(size))
                        .start(LogicalBlockAddress(start))
                        .finish();
                    new.add_partition(part);
                    //
                    let part = new.remove_partition(0);
                    new.add_partition(part);
                }
            }
        });
    }
}

#[cfg(not(fuzzing))]
fn main() {}
