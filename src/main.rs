#![allow(unused_imports, dead_code, unused_mut)]
use parts::*;
use std::io::Cursor;

fn main() {
    println!("Doing");
    let mut buff = std::fs::File::open("scratch/test_parts").unwrap();
    let gpt = Gpt::from_reader(buff);
    dbg!(&gpt);
    match gpt {
        Err(e) => {
            dbg!(e);
        }
        _ => (),
    }
}
