//! parts

pub mod gpt;
pub mod mbr;
pub mod util;

pub use gpt::*;
pub use mbr::*;
pub use util::*;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
