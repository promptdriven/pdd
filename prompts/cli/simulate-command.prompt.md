# Choose a simulation command

Own `src/simulate-command.mjs`, beside the simulation client. Export pure module function `chooseSimulationCommand({story,complete,cliEntries,httpRoutes,screens,hasDoor}) -> {kind,command,timeHint,reason}`. This is the single production command-choice function used by workflow advice; future issue #2760 must reuse it for automatic simulation dispatch. It does not execute, open, authenticate, approve or choose a Story. Existing explicit simulate flags and default dispatch remain unchanged by this issue.

The caller supplies the exact selected Story path and locally validated capability counts: all distinct scenario-linked CLI candidates carrying both exact input/result cli conventions, usable named HTTP routes and associated usable app-map screens. Count CLI candidates before program-name validation; unsafe or reserved names cannot erase multiple-candidate ambiguity. Null means unknown; zero is an established empty count. `complete` covers current scoped-source validation, including the complete transitive Runtime-call dependency closure; a sole CLI candidate also requires the existing CLI adapter's valid program name. An unusable sole candidate means incomplete/unknown evidence, never an established zero CLI count for fallback. `hasDoor` means a locally valid Story/scenario/Runtime-entry link. Counts are evidence, not filename or prose guesses; this module does not read files or call a service.

| Current evidence | kind and command |
|---|---|
| Incomplete, any unknown count, or no valid door | unknown; empty command |
| One or more screens | screen; `pdd simulate STORY` |
| No screens and exactly one CLI entry | cli; `pdd simulate STORY --cli --shell` |
| No screens and several CLI entries | unknown; empty command (the CLI adapter cannot choose one) |
| No screens/CLI and one or more HTTP routes | http; `pdd simulate STORY --serve` |
| Valid door, no screen/CLI/HTTP route | call; `pdd simulate STORY` (the existing Call form) |

Screen precedence preserves an app's normal page even when it also has API routes. A sole CLI takes precedence over HTTP when no screen exists. Positive outcomes have `timeHint: "about 2 minutes"` (a rough interaction hint, not a setup-duration promise), and reason `Story PATH has a Simulator door.` using the unquoted exact Story path. Unknown has empty command/timeHint and reason `PDD cannot determine this Story's runnable interface from current local evidence.`. Unknown never means skip.

Build the displayed command from literal words plus one safely POSIX-quoted Story argument: leave nonempty words matching `[A-Za-z0-9_./:@%+=,-]+` unquoted; otherwise enclose in single quotes and replace each embedded single quote with `'\''`. Reject an empty Story or one containing NUL/CR/LF with kind unknown and the same unknown reason. The command is advice only and must never become executed shell text inside this module. The exact Story path stays data, including spaces and shell metacharacters.

## Dependencies

None. The caller owns local evidence validation and supplies the declared counts. This module owns only the selection, exact command, time hint and reason. No outside port is needed for this pure public boundary.

<details>
<summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"2d0a9828885e7551bbe48ec58ba9184107a64ef72c3d7d40e31e7996434b2bb0","entries":[{"operation":"chooseSimulationCommand","input_schema":{"type":"object","properties":{"story":{"type":"string"},"complete":{"type":"boolean"},"cliEntries":{"oneOf":[{"type":"integer","minimum":0},{"type":"null"}]},"httpRoutes":{"oneOf":[{"type":"integer","minimum":0},{"type":"null"}]},"screens":{"oneOf":[{"type":"integer","minimum":0},{"type":"null"}]},"hasDoor":{"type":"boolean"}},"required":["story","complete","cliEntries","httpRoutes","screens","hasDoor"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"kind":{"type":"string","enum":["unknown","screen","cli","http","call"]},"command":{"type":"string"},"timeHint":{"type":"string"},"reason":{"type":"string"}},"required":["kind","command","timeHint","reason"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":1},"conventions":[]}
```
</details>
