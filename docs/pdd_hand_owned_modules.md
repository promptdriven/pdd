# Hand-owned PDD support modules

## `pdd/json_atomic.py`

`json_atomic.py` is a hand-owned durability primitive, not generated module
output. It is intentionally exempt from the one-prompt/one-module inventory:
it provides the narrowly scoped same-directory temporary-write, file fsync,
atomic replace, and directory fsync behavior used by generated and hand-owned
modules alike. Its ownership boundary is verified by direct callers and their
transactional failure tests; changes require tests for write, fsync, replace,
and cleanup failures. Do not add a generated prompt merely to satisfy module
counts unless this primitive acquires an independently regenerable interface.
