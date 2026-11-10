# Named local agent launcher configuration ports

I can load named local agent launcher definitions from `$HOME/.config/pdd/agents.json` with tilde expansion, deterministic SHA-256 custom IDs, and secret override registration while ignoring repository files and rejecting symlinks or invalid entries.

```pdd-boundary
prompts/cli/agent-config.prompt.md
```

## Acceptance criteria

1. When `$HOME/.config/pdd/agents.json` is absent, `loadAgentDefinitions` returns the built-in `codex`, `claude`, and `gemini` launchers without reading any repository `.pdd/agents.json` file.
2. When `$HOME/.config/pdd/agents.json` is valid, `loadAgentDefinitions` expands leading `~/` paths against `HOME`, assigns `custom-` plus the first 24 SHA-256 hex characters of the exact name, registers secret-named override values through `secrets.remember`, and appends built-in defaults unless `include_defaults` is false.
3. `loadAgentDefinitions` raises `invalid-agents-config` without reading contents or falling back when `$HOME/.config/pdd/agents.json` is a symbolic link or exceeds 65536 bytes.
4. `loadAgentDefinitions` raises `invalid-agents-config` without fallback when `$HOME/.config/pdd/agents.json` contains an unknown agent kind or a name that collides with an enabled default launcher.
