//! Gpt Definitions
use crate::mbr::*;
use crc::{crc32, Hasher32};
use serde::{Deserialize, Serialize};
use snafu::{ensure, ResultExt, Snafu};
use std::convert::TryInto;
use std::io::prelude::*;
use std::io::Cursor;
use std::io::SeekFrom;

#[derive(Debug, Snafu)]
pub struct GptError(InnerError);

#[derive(Debug, Snafu)]
enum InnerError {
    #[snafu(display("Invalid GPT Header Signature"))]
    Signature {},

    #[snafu(display("GPT Header Checksum Mismatch"))]
    ChecksumMismatch {},

    #[snafu(display("Error reading from device"))]
    Io { source: std::io::Error },

    #[snafu(display("Error parsing GPT Header structure"))]
    Parse { source: bincode::Error },

    #[snafu(display("{}", source))]
    MbrError { source: crate::mbr::MbrError },
}

type Result<T, E = GptError> = std::result::Result<T, E>;

/// The GPT Header Structure
#[derive(Default, Serialize, Deserialize)]
// Required because we do some messing around with the layout.
#[repr(C)]
struct GptHeader {
    /// Hard-coded to "EFI PART"
    signature: [u8; 8],

    /// Currently hard-coded to `1.0`/`0x00010000`, but may change?
    revision: u32,

    /// Must be header_size >= 92 and header_size <= logical block size
    header_size: u32,

    /// CRC32(bytes[0..header_size])
    header_crc32: u32,

    /// Must be zero
    _reserved: u32,

    /// The logical block address we reside in
    this_lba: u64,

    /// The logical block address the backup header is in
    alt_lba: u64,

    /// Where partitions can start
    first_usable_lba: u64,

    /// Where partitions must end
    last_usable_lba: u64,

    /// Disk GUID
    disk_guid: u128,

    /// Where our partition array starts on disk.
    partition_array_start: u64,

    /// Number of partitions
    partitions: u32,

    /// Size of each partition entry structure
    // Must be 128 * 2^n, where n >= 0
    partition_size: u32,

    /// CRC32 of the partition array
    // NOTE: Non-aligned? Makes entire structure 96 bytes instead of 92
    partitions_crc32: u32,
}

impl GptHeader {
    pub fn new() -> Self {
        Self::default()
    }

    /// Read the GPT Header from a `Read`er.
    ///
    /// The `Read`ers current position is undefined after this call.
    pub fn from_reader<R: Read + Seek>(mut source: R) -> Result<Self> {
        let mut obj: GptHeader = bincode::deserialize_from(&mut source).context(Parse)?;
        obj.check_validity(source)?;
        Ok(obj)
    }

    pub fn from_bytes(source: &[u8]) -> Result<Self> {
        let mut obj: GptHeader = bincode::deserialize(source).context(Parse)?;
        let source = Cursor::new(source);
        obj.check_validity(source)?;
        Ok(obj)
    }

    /// Checks the validity of the header
    ///
    /// # Errors
    ///
    /// The position of `source` is undefined on error.
    /// If it's important, save it.
    ///
    /// # Details
    ///
    /// Checks the Signature and header CRC, but not the partition array
    fn check_validity<R: Read + Seek>(&mut self, mut source: R) -> Result<(), InnerError> {
        ensure!(&self.signature == b"EFI PART", Signature);
        let old_crc = std::mem::replace(&mut self.header_crc32, 0);
        //
        let source_bytes =
            self as *const GptHeader as *const [u8; std::mem::size_of::<GptHeader>()];
        let source_bytes = unsafe { *source_bytes };
        // NOTE: Even with repr(C), size_of::<GptHeader>() == 96, not 92.
        // Even so, this seems to work anyway.
        let crc = crc32::checksum_ieee(&source_bytes[..self.header_size as usize]);
        ensure!(crc == old_crc, ChecksumMismatch);
        self.header_crc32 = old_crc;
        //
        // TODO: Verify header::this_lba is correct
        //
        // TODO: Support more block sizes
        source
            .seek(SeekFrom::Start(self.partition_array_start * 512))
            .context(Io)?;
        let mut buf: Vec<u8> = Vec::with_capacity((self.partitions * self.partition_size) as usize);
        buf.resize(buf.capacity(), 0);
        source.read_exact(&mut buf).context(Io)?;
        let crc = crc32::checksum_ieee(&buf);
        ensure!(crc == self.partitions_crc32, ChecksumMismatch);
        //
        Ok(())
    }
}

impl std::fmt::Debug for GptHeader {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("GptHeader")
            .field(
                "signature",
                &std::str::from_utf8(&self.signature).unwrap_or("<INVALID GPT>"),
            )
            .field("revision", &self.revision)
            .field("header_size", &self.header_size)
            .field("header_crc32", &self.header_crc32)
            .field("this_lba", &self.this_lba)
            .field("alt_lba", &self.alt_lba)
            .field("first_usable_lba", &self.first_usable_lba)
            .field("last_usable_lba", &self.last_usable_lba)
            .field("disk_guid", &self.disk_guid)
            .field("partition_array_start", &self.partition_array_start)
            .field("partitions", &self.partitions)
            .field("partition_size", &self.partition_size)
            .field("partitions_crc32", &self.partitions_crc32)
            .finish()
    }
}

#[derive(Default, Debug, Serialize, Deserialize)]
struct GptPart {
    /// Defines the type of this partition
    partition_type_guid: u128,

    /// Unique identifer for this partition
    partition_guid: u128,

    /// Where it starts on disk
    starting_lba: u64,

    /// Where it ends on disk
    ending_lba: u64,

    /// Attributes
    // TODO: Bitflags
    attributes: u64,

    /// Null-terminated name
    // FIXME: Proper string support.
    // [u8; 72]
    name: [u8; 32],
    name_2: [u8; 32],
    name_3: [u8; 8],
}

impl GptPart {
    pub fn new() -> Self {
        unimplemented!()
    }

    pub fn from_reader<R: Read + Seek>(mut source: R) -> Result<Self> {
        Ok(bincode::deserialize_from(&mut source).context(Parse)?)
    }

    pub fn from_bytes(source: &[u8]) -> Result<Self> {
        Ok(bincode::deserialize(source).context(Parse)?)
    }
}

#[derive(Debug, Default)]
pub struct Gpt {
    mbr: ProtectiveMbr,
    header: GptHeader,
    partitions: Vec<GptPart>,
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
        let header = GptHeader::from_reader(&mut source)?;
        let mut partitions = Vec::with_capacity(header.partitions as usize);
        // TODO: Support more block sizes
        source
            .seek(SeekFrom::Start(header.partition_array_start * 512))
            .context(Io)?;
        for _ in 0..header.partitions {
            partitions.push(GptPart::from_reader(&mut source)?);
        }

        //
        Ok(Self {
            //
            mbr,
            header,
            partitions,
        })
    }

    pub fn from_bytes(_source: &[u8]) -> Result<Self> {
        unimplemented!()
    }

    pub fn from_file() -> Self {
        unimplemented!()
    }
}
