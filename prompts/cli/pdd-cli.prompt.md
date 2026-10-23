# PDD command runner

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/pdd-cli.mjs`. Export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Parse before doing any work and act only on a catalogued command ID. Help, version, skill output, completion, and workflow listing run from public source without importing Host. Host commands receive only the parser's reconstructed argument vector and use the installed Host export. Return `0` after successful local work, `2` for command or option errors, `1` for missing skill or other local/runtime failures, `69` when a Host command has no installed Host, and the Host's integer result when it returns one. Write diagnostics to stderr; do not print raw invalid arguments.

When Host cannot load, retain exit 69 and show a fixed diagnostic distinguishing a missing entry, a load/dependency failure, an incompatible export, or an unknown unavailability. Point to the packaged setup guide for supported distribution availability; do not promise installation or repair instructions that are not yet published. Never echo raw import exceptions. Help must describe this recovery behavior without claiming installed acceptance.
