# hash

`hash.mjs` exports module function `fingerprint(compute, text)`. Return `{value}` from exactly one compute.hash_utf8 call with the unchanged text. This computes lowercase hexadecimal SHA-256 of exact UTF-8 bytes, with no trimming, newline insertion or JSON serialization.

## Dependencies

None.
