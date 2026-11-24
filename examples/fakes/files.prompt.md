# files

`files.mjs` exports module function `readNote(files, path)`. Read exactly once with the injected files.read callback and return its `{content}` unchanged. The runtime files resource binds UTF-8 content by exact POSIX path; this example accepts existing regular files only.

## Dependencies

None.
