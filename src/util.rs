//! Utilities

/// (De)Serialize the GPT partition name, as a fixed size byte array.
///
/// Handles the conversion to/from UCS-2, currently by assuming it's valid UTF-16.
///
/// Supports serializing from anything that implements `AsRef<[u8]>`,
/// and deserializing to `String`
pub mod partition_name {
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
