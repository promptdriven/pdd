# Own-agent adapters ports

I can parse local agent status, discover installed agents through read-only process probes, and validate a chosen agent's structured Try reply.

```pdd-boundary
prompts/cli/agent-adapters.prompt.md
prompts/cli/agent-config.prompt.md
```

## Acceptance criteria

1. parseAgentAuthStatus returns ready, signed_out, or unavailable directly from the supplied status observation. An unknown agent or malformed result returns unavailable.
2. discoverAgents loads default definitions through the shared agent-config owner when none are supplied, then checks help and authentication status. It reports not_installed only when the process observation proves the executable is missing.
3. askAgent validates a fill against the selected entry's complete input schema. It preserves run=true only when supportsRun, supportsApply, apply=true, and a valid fill are present. Other optional fields survive only when they pass their native rules.
4. An unknown agent returns a structured failure with fill=null and no subprocess call. runAgentProcess returns {code, stdout, stderr} on success.
