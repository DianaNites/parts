//! Gpt Definitions
use crate::mbr::*;
use crc::crc32;
use serde::{Deserialize, Serialize};
use snafu::{ensure, ResultExt, Snafu};
use std::io::{prelude::*, Cursor, SeekFrom};

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

mod signature {
    use serde::{
        de::Error as _,
        ser::{Error as _, SerializeTuple as _},
        Deserialize, Deserializer, Serializer,
    };

    pub fn serialize<T, S>(data: T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: AsRef<[u8]>,
    {
        let data = data.as_ref();
        if data.len() != 8 {
            return Err(S::Error::custom("Invalid GPT Signature"));
        }
        //
        let mut tup = serializer.serialize_tuple(8)?;
        for byte in data {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<String, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes: [u8; 8] = <[u8; 8]>::deserialize(deserializer)?;
        String::from_utf8(bytes.to_vec()).map_err(D::Error::custom)
    }
}

mod partition_name {
    use serde::{
        de::Error as _,
        ser::{Error as _, SerializeTuple as _},
        Deserialize, Deserializer, Serializer,
    };

    pub fn serialize<T, S>(data: T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: AsRef<str>,
    {
        let data = data.as_ref();
        if data.len() >= 36 {
            return Err(S::Error::custom("Invalid Partition Name, too long"));
        }
        //
        let buf: Vec<u16> = data.encode_utf16().collect();
        assert!(buf.len() < 36);
        // TODO: Verify UCS-2?
        let mut tup = serializer.serialize_tuple(36)?;
        for byte in &buf {
            tup.serialize_element(byte)?;
        }
        // Null-init any remainder
        for _ in 0..36 - buf.len() {
            tup.serialize_element(&0u16)?;
        }
        tup.end()
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<String, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Using u32 because of technical limitations, array impls limited to 32.
        // 72 / 4 == 18
        let bytes: [u32; 18] = <[u32; 18]>::deserialize(deserializer)?;
        // Partition names are UCS-2
        let bytes: *const [u16; 36] = &bytes as *const [u32; 18] as *const [u16; 36];
        let bytes: [u16; 36] = unsafe { *bytes };
        //
        let mut s = String::from_utf16(&bytes).map_err(D::Error::custom)?;
        // Strip nul bytes
        s.retain(|c| c != '\0');
        //
        Ok(s)
    }
}

/// The GPT Header Structure
#[derive(Default, Debug, Serialize, Deserialize)]
pub struct GptHeader {
    /// Hard-coded to "EFI PART"
    #[serde(with = "signature")]
    signature: String,

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
    /// Checks the Signature, header CRC, and partition array CRC.
    fn check_validity<R: Read + Seek>(&mut self, mut source: R) -> Result<(), InnerError> {
        ensure!(&self.signature == "EFI PART", Signature);
        let old_crc = std::mem::replace(&mut self.header_crc32, 0);
        // Relies on serialization being correct.
        let source_bytes = bincode::serialize(&self).context(Parse)?;
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

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct GptPart {
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

    /// Null-terminated name, UCS-2 string,
    /// max length of 36 including null.
    #[serde(with = "partition_name")]
    name: String,
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
        Self::default()
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
