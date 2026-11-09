# Local shell completion

Own `src/completion.mjs`; export `renderCompletion(shell)`. Derive suggestions only from the local command catalog, including supported option names and shell operands. Return newline-terminated bash or zsh script, otherwise TypeError. Shell scripts must be usable when loaded by that shell. Do not suggest excluded commands or invoke any application/backend during completion.

## Dependencies

- [Command catalog](command-catalog.prompt.md): required authoring/generation/verification/testing context for canonical command/option suggestions.

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for scope and the shared local command contract.

The words test, lint, simulate and run are the [NAMES](command-catalog.prompt.md#names) words. Offer only these words, never a removed or quiet word (`check`, `try`, `sim`, `workflow start`).

Offer the catalog's workflow routes and supported options, including --said for approval. For NAME after workflow run, obtain validated actual project+bundled names from local `pdd workflow list --json`; this local read is the sole exception to the no-application-call completion rule. Parse only its JSON workflows name fields via installed Node, keep safe names, never shell-evaluate output or invoke workflow execution/native/network. Invalid/unavailable listing yields no names. Keep catalog-owned option choices and complete them at any argument position, including after NAME and ISSUE.

Offer `test`, `lint` and `simulate` with their options and the `--tab` choices. Never offer an option marked `hidden` (`--request`, and `--lint` and `--local` on `test`).

Choice completion is scoped to the command prefix as well as the option: workflow --agent offers only codex/claude, while simulate --agent offers codex/claude/gemini, at any argument position. A same-named option on another command cannot widen choices.

Runtime transport: each entry names the public operation above. JSON-text fields are explicitly described in their schemas and are decoded before using the public value; the result field `value` encodes the complete public return value where its shape is dynamic. Other scalar/array returns use the named result wrapper. An empty result object represents a void return. Optional fields retain the native defaults. These transport wrappers do not add native exports or change domain decisions. Execution limits below are draft check budgets, not public input limits.

This entry renders the script only. Loading it in bash/zsh and its local workflow-name subprocess still require native shell tests.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft",
  "prose_sha256": "5b0eb769aa8c19d50f167351631f6be05e75601a76fc38cfa1e81eaf4ae7a75e",
  "entries": [
    {
      "operation": "renderCompletion",
      "input_schema": {
        "type": "object",
        "properties": {
          "shell": {
            "type": "string"
          }
        },
        "required": [
          "shell"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "text": {
            "type": "string"
          }
        },
        "required": [
          "text"
        ],
        "additionalProperties": false
      },
      "errors": [
        "TypeError"
      ],
      "resource_operations": []
    }
  ],
  "calls": [],
  "resources": [],
  "limits": {
    "max_steps": 64,
    "max_model_calls": 16
  },
  "conventions": []
}
```
</details>
