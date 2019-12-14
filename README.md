# Parts

[![standard-readme compliant](https://img.shields.io/badge/readme%20style-standard-brightgreen.svg?style=flat-square)](https://github.com/RichardLitt/standard-readme)
![Maintenance](https://img.shields.io/maintenance/yes/2019?style=flat-square)
![GitHub Release Date](https://img.shields.io/github/release-date/DianaNites/parts?style=flat-square)
![GitHub commit activity](https://img.shields.io/github/commit-activity/w/DianaNites/parts?style=flat-square)
![Crates.io](https://img.shields.io/crates/v/parts?style=flat-square)
![GitHub release (latest SemVer)](https://img.shields.io/github/v/release/DianaNites/parts?sort=semver&style=flat-square)
![Crates.io](https://img.shields.io/crates/l/parts?style=flat-square)
![GitHub issues](https://img.shields.io/github/issues/DianaNites/parts?style=flat-square)
![GitHub pull requests](https://img.shields.io/github/issues-pr/DianaNites/parts?style=flat-square)
![Liberapay patrons](https://img.shields.io/liberapay/patrons/DianaNites?style=flat-square)
![Crates.io (latest)](https://img.shields.io/crates/dv/parts?style=flat-square)

A GPT Partition Manager.

Parts is both a library and a binary tool to manage GPT partition labels,
written in pure Rust.

Parts allows you to read, write, and manipulate GPT tables in a safe and
efficient manner.

## Install

```shell
cargo install parts
```

```toml
[dependencies]
parts = "0.1.0"
```

## Usage

NOTE: Please don't use this, it's new, WIP, and untested.
Back up your data, or only use it on virtual disks.

The code is well documented but unpolished, and the API is unstable.

This example opens a disk image file, and adds a partition.

```rust
use parts::{Gpt, GptPartBuilder, types::*};
use std::fs::File;
const PATH: &str = "tests/data/test_parts";

// A reasonable default block size.
const BLOCK_SIZE: BlockSize = BlockSize(512);

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut gpt = Gpt::from_reader(File::open(PATH)?, BLOCK_SIZE)?;
    let part = GptPartBuilder::new(BLOCK_SIZE)
        .name("Example")
        .size((BLOCK_SIZE * 2).into())
        .start(34.into())
        .finish();
    gpt.add_partition(part);
    // This is left as an exercise to the reader.
    // gpt.to_writer(output_file);

    Ok(())
}
```

<!-- TODO: CLI Example here -->

## Features

<!-- TODO: Optional crate features -->

## Contributing

Feel free to ask questions on the [Github repo](https://github.com/DianaNites/parts).

[See CONTRIBUTING.md](CONTRIBUTING.md) for details on code contributions.

## License

Licensed under either of

* Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0)>
* MIT license
   ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT)>

at your option.
