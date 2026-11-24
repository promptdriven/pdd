# hash

As a developer testing a fingerprinting module, I want to hash exact UTF-8 input deterministically, so that the digest matches standard SHA-256 output.

## Acceptance criteria

1. The fingerprint of "abc" returns its lowercase hexadecimal SHA-256 digest without modifying the input bytes.
