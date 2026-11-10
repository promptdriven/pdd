# Resolve and validate chat launch profiles through Runtime ports

I can compute deterministic Herdr agent names, merge requested launch profile options, preserve a higher Codex `config.toml` thread limit, and validate saved profiles through declared compute and blob ports.

```pdd-boundary
prompts/cli/workflow-launch-profile.prompt.md
```

## Acceptance criteria

1. `launchProfile` computes the deterministic `pdd-` plus 12-hex prefix from `repository` and `runId` and fails with `invalid_launch_profile` when the agent is unsupported.
2. `chatAgentName` appends `-` plus 6-hex from `repository`, `runId` and `area` to the profile prefix and fails with `invalid_launch_profile` when `area` is empty.
3. `selectLaunchProfile` reads `config.toml` under `configDir` when a Codex thread limit is requested, preserves a higher `features.multi_agent_v2.max_concurrent_threads_per_session` limit, and fails with `invalid_launch_profile` on a leading-dash model or invalid option.
4. `validLaunchProfile` accepts a saved profile whose effective Codex thread limit exceeds 8, and fails with `invalid_launch_profile` when `requireValid` is `true` on an invalid profile.
