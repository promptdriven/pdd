# Inspect the call cap before paid work

As a PDD user, I want to inspect a selected call cap before paid work, so that I can see structural cost warnings without spending AI calls.

## Acceptance criteria

1. The zero-AI call preflight display shows the supplied estimate of 29 calls against cap 25, ordered step costs 13 and 16, source and engine identity, and a warning that leaves the cap unchanged.
2. A supplied within-estimate result of 20 calls against cap 25 stays advisory and gives no guarantee of actual calls or completion; resource continuations are not included.
3. An incomplete unknown report keeps its total and step cost unknown and makes no cap-fit claim.
4. A missing or inconsistent source, engine or selected-cap association shows preflight unavailable and makes no estimate or cap-fit claim.

```pdd-boundary
prompts/cli/lint-call-preflight.prompt.md
```

## Rules to check

Only source- and cap-associated reports with a known engine can display a structural estimate or warning. Missing or inconsistent context cannot claim a fit. Rendering never changes supplied facts.

## Verification boundary

The prompt scenario checks the pure advisory display with synthetic server facts.
Native transport tests separately cover the real CLI flag, cap forwarding, zero
paid dispatch, server JSON preservation, saved reads and old-server refusal.
These transport effects are not claimed as prompt-interpreter evidence.
