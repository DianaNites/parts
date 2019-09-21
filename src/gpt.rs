//! Gpt Definitions
use crate::mbr::*;
use snafu::{ResultExt, Snafu};
use std::io::prelude::*;

#[derive(Debug, Snafu)]
pub struct GptError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid GPT Header: {}", source))]
    InvalidGptHeader { source: std::io::Error },

    #[snafu(display("{}", source))]
    MbrError { source: crate::mbr::MbrError },
}

type Result<T, E = GptError> = std::result::Result<T, E>;

#[derive(Debug)]
struct GptHeader {
    //
}

#[derive(Debug)]
pub struct Gpt {
    mbr: ProtectiveMbr,
    header: GptHeader,
}

impl Gpt {
    pub fn new() -> Self {
        unimplemented!()
    }

    /// Read from an existing GPT Disk
    pub fn from_reader<RS>(mut source: RS) -> Result<Self>
    where
        RS: Read + Seek,
    {
        let mbr = ProtectiveMbr::from_reader(&mut source).context(MbrError)?;
        let header = GptHeader {};
        Ok(Self {
            //
            mbr,
            header,
        })
    }

    pub fn from_file() -> Self {
        unimplemented!()
    }
}
