# Choose an available signed-in workflow agent

Own `src/workflow-agents.mjs`. Share readiness and selection between setup and workflow startup; a signed-out or missing optional agent must not block a ready one. Ready means credentials configured, not a successful provider authentication; expired/revoked credentials are not detected by status. This module does not start a chat, install a tool, change authentication, read credential files, or allocate a worktree. Its decisions are based on the native CLIs' noninteractive authentication-status commands, with the caller's HOME, PATH, CODEX_HOME and CLAUDE_CONFIG_DIR unchanged. Try-page read-only capability checks are a separate policy.

Export module functions `chooseWorkflowAgent({codex,claude,requested})` and `checkWorkflowAgents({cwd,env,requested},ports)`. The pure chooser receives readiness states `ready`, `missing`, `signed_out` or `unavailable`; requested is absent, `codex` or `claude`. Return `{ok,agent,message}`, with a selected agent and empty message on success, otherwise null agent and plain actionable guidance. Invalid states are unavailable; invalid requested names refuse without a probe.

| Choice | Outcome |
| --- | --- |
| Explicit agent | Use it only if ready; never silently switch to the other agent. |
| No explicit agent, Codex ready | Select Codex, including when both are ready. |
| No explicit agent, only Claude ready | Select Claude. |
| Neither ready | Refuse with installation/sign-in/status guidance for the states actually observed. |

Both missing: say `Install Codex or Claude Code first.` and provide the official install links. Otherwise give one actionable line for each unavailable candidate: missing means install that agent; signed_out means `Codex is not signed in. Run: codex login` or `Claude Code is not signed in. Run: claude auth login`; unavailable means its sign-in could not be checked and gives its status command. Never display raw authentication stdout/stderr, user/account details, credentials or config paths. One ready candidate makes an unselected candidate's failure irrelevant.

`checkWorkflowAgents` uses an injectable async `ports.run(command,argv,options)` (default the existing native process runner). Check both candidates in parallel when no agent is requested, with the whole pair bounded by one status-probe wait rather than two sequential waits; an explicit request checks only that candidate. Run only `codex login status` or `claude auth status`; do not run login/logout, interactive prompts, a model query, or unrelated tool commands. Use the supplied cwd/env, closed stdin, at most 16 KiB output and the native status-probe wait bound of 10 seconds. No version pin, HOME/config inference, credential lookup, cached readiness or fallback to another environment.

A native ENOENT counts as missing only with the process port's explicit executableMissing evidence. Otherwise it is unavailable, including a missing cwd, missing shebang interpreter or an uncertain injected error. Delegate response interpretation to [the shared credential-status owner](agent-adapters.prompt.md#shared-credential-status-interpretation) parseAgentAuthStatus. Transport failures, interrupted/overlong responses and untyped status remain unavailable; wrapper banners cannot establish Claude readiness. Do not infer readiness from a config folder or another agent's result.

## Dependencies

- Load the [Prompting guide](../../docs/prompting-guide.md) for authoring and generation.
- [Agent adapters](agent-adapters.prompt.md) owns the reusable `runAgentProcess` native process boundary, including closed input, process cleanup, bounded output, executableMissing evidence and the shared parseAgentAuthStatus credential-status rules. This module supplies only status commands, the caller environment and the probe bounds; it does not use Try discovery or invoke the model adapter.
- The [CLI](pdd-cli.prompt.md) and [runner](workflow-runner.prompt.md) own setup/startup dispatch and all subsequent effects. A refused readiness result must not be interpreted as a started workflow. They do not infer readiness themselves.
- Native command reference: [Claude Code CLI](https://code.claude.com/docs/en/cli-reference). Commands and accepted readiness facts are specified above so generation does not depend on a live documentation fetch.

<details>
<summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "d5bb173f1234f16ff9559afdc031335e9ad48bfd4e88e4aa8b3157a777279f6e",
  "entries": [{
    "operation": "chooseWorkflowAgent",
    "input_schema": {
      "type": "object",
      "properties": {
        "codex": {"type": "string", "enum": ["ready", "missing", "signed_out", "unavailable"]},
        "claude": {"type": "string", "enum": ["ready", "missing", "signed_out", "unavailable"]},
        "requested": {"type": "string", "enum": ["codex", "claude"]}
      },
      "required": ["codex", "claude"], "additionalProperties": false
    },
    "result_schema": {
      "type": "object",
      "properties": {
        "ok": {"type": "boolean"},
        "agent": {"oneOf": [{"type": "string", "enum": ["codex", "claude"]}, {"type": "null"}]},
        "message": {"type": "string"}
      },
      "required": ["ok", "agent", "message"], "additionalProperties": false
    },
    "errors": []
  }],
  "calls": [], "resources": [],
  "limits": {"max_steps": 1, "max_model_calls": 1}, "conventions": []
}
```

</details>
