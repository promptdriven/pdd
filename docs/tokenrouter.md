# TokenRouter

PDD supports TokenRouter as a first-class local-mode provider. Configure
`TOKENROUTER_API_KEY`, run `pdd setup`, and select **TokenRouter** when setup
asks which configured providers to keep. Its canonical API base is
`https://api.tokenrouter.com/v1`.

## Deterministic model catalog

TokenRouter availability changes more frequently than a PDD release. PDD does
not query `/v1/models` during inference. Instead, each release ships a reviewed
snapshot of the intersection between:

1. text models already supported by PDD, and
2. models TokenRouter exposes with a protocol the bundled LiteLLM can call.

The current snapshot is declared in `pdd/tokenrouter.py`, and the corresponding
`TokenRouter` rows are in `pdd/data/llm_model.csv`. Re-running setup adds those
rows when `TOKENROUTER_API_KEY` is configured. Setup's normal provider
selection can keep TokenRouter and remove only pristine PDD-managed rows for
unselected cloud providers; direct-provider rows you retain or customize, and
local/device-only rows, follow the existing preservation rules.

The intersection is based on model identity across every supported PDD route,
not only direct API-provider rows. For example, Claude Sonnet 4 is supported by
PDD through GMI Cloud and GitHub Copilot, GPT-5 Mini through OCI, Copilot, and
Perplexity, and GPT-5.6 Sol through the ChatGPT subscription route. Their
TokenRouter routes are included while those existing rows remain unchanged.

The snapshot has explicit routes for:

- `openai`: LiteLLM OpenAI chat completions
- `openai-response`: LiteLLM's Responses bridge
- `anthropic` and `anthropic-compatible`: Anthropic Messages
- `gemini`: native Gemini `generateContent`

Anthropic calls are normalized to
`https://api.tokenrouter.com/v1/messages` because LiteLLM otherwise appends a
second `/v1/messages` suffix to the canonical `/v1` base.

PDD deliberately excludes image, video, audio-only, embedding, rerank, and
other non-text entries. It also excludes TokenRouter text models not already in
PDD's supported catalog and any unknown endpoint type. A catalog entry is never
treated as OpenAI chat merely because it is reachable through the same host.

## Exact request-scoped routing

Services that handle concurrent requests must not set `PDD_MODEL_DEFAULT` or
other process-wide environment variables per request. Use the library API:

```python
from pdd.llm_invoke import llm_invoke

result = llm_invoke(
    messages=[{"role": "user", "content": "Explain this change."}],
    model="openai/responses/openai/gpt-5.4",
    model_provider="TokenRouter",
    use_cloud=False,
)
```

`model` is the exact `model` column value and `model_provider` is the CSV
provider display name. The pair resolves one row, bypasses strength selection,
and does not mutate environment state. Missing or ambiguous rows fail closed
instead of falling back to another model or provider. `model_provider` requires
`model`. When both are omitted, existing strength-based routing is unchanged.

The hosted JSON spelling used by PDD Cloud is `modelProvider`; the Python
library spelling is `model_provider`. PDD Cloud must resolve a public
TokenRouter model ID (for example `openai/gpt-5.4`) to the packaged route ID
(for example `openai/responses/openai/gpt-5.4`) before calling this API.

Exact local selection is intentionally incompatible with `use_cloud=True`;
passing both raises an error rather than silently discarding the requested
route.
