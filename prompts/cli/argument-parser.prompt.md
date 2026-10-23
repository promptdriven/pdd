# Public argument parser

Follow `public-boundary.prompt.md` for shared public naming and closed-source boundaries.

Own `src/argument-parser.mjs`. Export `CommandInputError` and `parseArgv(argv)`. Resolve the longest exact route prefix from `PUBLIC_COMMAND_ROUTES`, validate the declared operands and options, and return a plan with a catalogued `commandId`, local disposition, typed values, and a newly reconstructed `hostArgv`. Reject unlisted commands, options, malformed values, and invalid option combinations with `CommandInputError` carrying `exitCode: 2`. Do not return or forward the caller's original array.

For hosted Try, accept `--terminal` with optional `--session` and `--command`; a session is not required for an explicit terminal command. Without a session, reject `--input`, `--repeat`, and `--request` in terminal mode. With a session, allow either `--command` or the read-only `--request`, never both. Preserve the command text as one option value when reconstructing Host arguments.
