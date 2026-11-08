# Find a complete after-step example

As a person adding a second operation after a tap, I can find a complete valid app-map example and understand where its result goes, and I can understand an invalid after-step refusal.

## Acceptance criteria

- The app-map guide shows a complete example with an `after` entry whose `handler` contains `prompt_path` and `operation`, with `input` and `bind`. It explains that the bound result goes into app state.
- An `invalid-after-step` refusal gives field-level guidance for the nested `handler` shape while retaining a more specific server reason, server fix and reported location.
- The guide explains the scope of ordinary Story lint and explains that a new simulation with a selected app map reaches full-engine admission and execution, with its cost, and that the file-selection preview is not validation. It does not invent a dedicated validation command.
- Existing app-map behavior, other refusal explanations and server-owned validation do not change.

## Rules to check

- A flat after entry with `prompt_path` and `operation` at the entry level is not the nested `handler` shape; a generic `invalid-after-step` refusal must not leave the required `handler` field unnamed.
- A supplied server reason and fix take precedence over local fallback guidance, and a reported location remains visible; the fallback must not overwrite them.
- `bind` identifies a state location for the operation result; the guide must not claim that it binds only one result field or validates server effects locally.
