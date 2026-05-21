# Story: Cost tracker utility

Covers the cost tracker prompt used by the contract-commands E2E demo.

## Glossary

- **calculate_cost**: Returns USD total for token usage including cache write/read multipliers.
- **model family**: Canonical pricing key resolved from a versioned model string.

## Covers

- cost_tracker_with_contracts_python.prompt#R1 — `calculate_cost` validates token counts and model string.
- cost_tracker_with_contracts_python.prompt#R2 — Known Claude families resolve via prefix/substring matching.
- cost_tracker_with_contracts_python.prompt#R3 — Cache write tokens use 1.25× input rate; cache read use 0.10× input rate.

## Oracle

- `calculate_cost("claude-3-7-sonnet-20250219", 1_000_000, 0)` returns input-rate USD for 1M tokens.
- Unknown model raises `ValueError` listing supported families.

## Negative Cases

- Negative token counts raise `ValueError`.
- Empty model string raises `ValueError`.
