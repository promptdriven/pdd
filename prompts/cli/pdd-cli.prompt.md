# PDD command runner

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/pdd-cli.mjs`. Export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Parse before doing any work and act only on a catalogued command ID. Help, version, skill output, completion, and workflow listing run from public source without importing Host. Host commands receive only the parser's reconstructed argument vector and use the installed Host export. Return `0` after successful local work, `2` for command or option errors, `1` for missing skill or other local/runtime failures, `69` when a Host command has no installed Host, and the Host's integer result when it returns one. Write diagnostics to stderr; do not print raw invalid arguments.
