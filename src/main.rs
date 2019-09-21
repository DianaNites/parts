#![allow(unused_imports, dead_code, unused_mut)]
use parts::*;
use std::io::Cursor;

fn main() {
    println!("Doing");
    let mut buff = Cursor::new(vec![0; 15]);
    let gpt = Gpt::from_reader(buff);
    dbg!(&gpt);
}
