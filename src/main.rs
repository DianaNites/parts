use parts::*;
use std::{io::Cursor, path::Path};

fn main() {
    let read_path = Path::new("scratch/test_parts");
    // let write_path = Path::new("scratch/test_parts_write");
    //
    let buff = std::fs::File::open(read_path).unwrap();
    let gpt = Gpt::from_reader(buff, 512).unwrap();
    // dbg!(&gpt);
    //
    let v = Vec::new();
    let mut buff = Cursor::new(v);
    gpt.to_writer(&mut buff).unwrap();
    //
    buff.set_position(0);
    let new_gpt = Gpt::from_reader(buff, 512).unwrap();
    // dbg!(&new_gpt);
    dbg!(new_gpt == gpt);
}
