# Data used by tests

## Files

### `test_parts`

An empty 10MiB file, created with gnu parted. Treated as if a 512 block size.

GPT label, one ext4-labeled partition, name "Test",
starting at 1MiB and ending at 9MiB, for a partition size of 8MiB.

### `test_parts_cf`

An empty 10MiB file, created with cfdisk. Treated as if a 512 block size.

GPT label, one "Linux filesystem data", no name.
starting at 1MiB and ending at 9MiB, for a partition size of 8MiB.

`cfdisk` automatically aligns on 1MiB, unlike parted.
