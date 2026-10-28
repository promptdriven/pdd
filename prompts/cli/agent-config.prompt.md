# Named local agents

`src/agent-config.mjs` owns the local list of the person's agent launchers. Export synchronous `loadAgentDefinitions({cwd,env=process.env})`, returning fresh records `{id,name,kind,command,env}`. `env` contains only overrides; the adapter merges these into the child environment. This new interface does not execute commands, change settings, read credentials or transmit configuration to the server.

Choose one file: `$HOME/.config/pdd/agents.json` when present, otherwise `.pdd/agents.json` at the nearest Git repository root containing `cwd`. Without a Git root, use `cwd`. If neither exists, return defaults. A selected user file wins completely, including when invalid: never recover by reading a repo file. A file must be regular, not a symlink, and at most 65536 bytes. Reject a symlinked repo `.pdd` directory. User configuration directory symlinks are permitted, supporting user-managed config directories. Read the selected file without following a final symlink and verify the byte bound on the actual read.

The JSON root is an object containing `agents` (required array, at most 24 entries) and optional boolean `include_defaults`; reject other properties. Each entry has exactly `name`, `kind`, `command`, and optional `env`. Names are nonempty, trimmed, unique, at most 100 characters and contain no controls. Kinds are `codex`, `claude`, `gemini`. Commands are nonempty strings, at most 4096 characters and contain no controls; spaces are literal executable-path characters, never shell syntax. Environment overrides are objects with at most 64 keys matching `[A-Za-z_][A-Za-z0-9_]*`; values are strings at most 8192 characters without NUL. Never interpolate variables or evaluate strings.

Expand leading `~` or `~/` in commands and environment values using the supplied HOME; other tildes remain literal. Refuse tilde expansion when HOME is unavailable. Relative command paths containing a slash resolve against the selected config directory, while program names remain PATH lookups. Absolute paths remain paths. Reject duplicate names, including collisions with enabled default display names or their lowercase IDs. Custom IDs are `custom-` followed by the first 24 lowercase hex characters of SHA-256 of the exact name; stable names retain IDs across reorderings and launcher edits.

Append defaults unless `include_defaults` is false: `{id:'codex',name:'Codex',kind:'codex',command:'codex',env:{}}`, then corresponding `claude`/`Claude` and `gemini`/`Gemini` records. An empty list with defaults disabled is valid. Invalid, unreadable or oversized files throw plain errors identifying the configuration problem, including unknown kind or missing command, without quoting file contents, command text, names or environment values. No fallback on a selected-file failure.

## Dependencies

Node built-in filesystem, path and crypto modules provide local bounded reads, path resolution and stable hashes. No project or provider dependency is required.
