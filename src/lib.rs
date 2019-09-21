//! parts
#![allow(unused_imports, dead_code)]

pub mod gpt;
pub mod mbr;

pub use gpt::*;
pub use mbr::*;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
