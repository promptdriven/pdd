# Human boundary card

Own `src/human-boundary-card.mjs`. It reads local repository files and saved `pdd test` records to build a compact, advisory 1-screen Human Boundary Card (`<= 25` lines) for `pdd approve` and PR 1 (`layout: "spec"`). It never calls GitHub, Herdr, the PDD interpreter or a model, never writes a file, and never blocks approval, PR publication, exploratory standalone simulations or `kind: "native-only"` prompts.

## Purpose

A person approving a prompt or reviewing PR 1 must see, on one screen above raw schema and prose details:

1. **Owned policy and invariants:** the slice's Story policy rules (its `## Rules to check` forbidden outcomes and numbered criteria) or, when no Story applies, the prompt's boundary role.
2. **Source and observation provenance per consequential rule or criterion check:**
   - Which owning prompt or code boundary was actually exercised by the scenario vs. whether an owning source or rule has a **`missing owner connection`**.
   - What kind of observation backed the check: `supplied fact`, `model-returned value`, `observed simulated port call` (including explicit `0 observed port calls` where a port is instrumented), or `native test`.
   - Whether `port spy or native observation still needed` applies because an effect, command or outbound action is reported only inside model-returned data (`result` or `world`) without an observed port call or native test.
3. **Verification split:** Runtime-checked operations vs. `kind: "native-only"` declarations (with their `reason`) and `## Native validation` / native test responsibilities, preserving the `native-only` route.
4. **Complexity budget and advisory divergences:** prompt prose line counts (`> 500` warning, `> 1000` elevated), Story scenario step counts (`> 15` steps or `> 1000` lines warning), and any saved multi-sample divergences across samples or reruns, shown strictly as advisory notes.

## Source selection and missing owner connection

Export `buildHumanBoundaryCard({root, focusPrompt = null, promptPaths = [], storyPaths = [], changedPaths = null, since = 0, env = process.env})`.

For each matched Story scenario (`schema_version: "prompt-runtime.program-scenario.v1"`):

1. **Selected source closure:** start from each step's `entry_path` (or the prompt declaring `step.operation` among `entry_path`, `entry_paths` and any Story `pdd-boundary` prompt list) and follow transitive `## Dependencies` prompt links (`promptMarkdownTargets`, retaining any `#fragment` heading target), `interface.calls[].target` prompt paths and `context` prompt paths inside the Git-visible repository.
2. **Owning sources in scope:** collect `focusPrompt` (for `pdd approve`), changed `*.prompt.md` files in the slice (`promptPaths` or Git changes against `HEAD` / `main`), Story `pdd-boundary` prompts and any Git-visible `*.prompt.md` explicitly named in the Story. Exclude misplaced test prompts and `kind: "native-only"` prompts from required Runtime scenario loading (`native-only` prompts appear under the native side of the verification split with their `reason`).
3. **Missing owner connection:** never credit a passing scenario to an unexercised owner or a disconnected rule:
   - **Unloaded owning source:** if any checkable owning prompt in scope is absent from the scenario's selected source closure (for example, a standalone simulator prompt passes checks while changed implementation or guide prompts are never linked or loaded, or a `## Dependencies` link to the owner was removed), record `missing owner connection` naming the unloaded owning source and the selected source that actually ran.
   - **Broken section or removed owning rule in selected source:** if a `## Dependencies` or Story link targets `owner.prompt.md#section` whose heading slug is absent from `owner.prompt.md`, or if a consequential rule or criterion (with salient domain terms or backticked policy identifiers) has zero matching domain stems or identifiers in the selected prompt closure's prose and Runtime interface while a synthetic scenario still passes, record `missing owner connection` (`rule absent from selected source`) for that rule/criterion instead of crediting the selected owner.

## Observation kinds

Classify each check on a criterion or rule into one of four observation kinds:

- **`observed simulated port call`:** a check with `target: "calls"` or saved check step evidence on an instrumented port (`interface.resources`, `interface.calls`, `simulation` or `simulation_overrides`). Explicitly report **`0 observed port calls`** whenever a `target: "calls"` check asserts `0` (or `[]`), or when a port is instrumented on the selected prompt/scenario and the saved check or step assertions record `0` calls on that port.
- **`supplied fact`:** a `result` or `world` check (with no observed port call or native test) whose asserted value was already supplied unchanged in `step.input` (`ref_target: "input"`, or a matching input key/non-boolean value) or unchanged at the same path in `initial_world`.
- **`model-returned value`:** a `result`, `world` or `error` check produced by the interpreter model without an observed simulated port call or native test and not a `supplied fact`. When the check inspects returned effect, action, call, alert, event or command claims (such as `/effects`, `/commands`, `/actions`, `/calls`, `/sent`, `/events` or effect-Bearing objects) without a `target: "calls"` check or native test on that criterion, append **`(port spy or native observation still needed)`**.
- **`native test`:** backed by a `kind: "native-only"` prompt declaration (retaining its `reason`), a Story `## Native validation` section, or saved native criterion evidence.

## Saved check records and advisory divergences

Inspect saved check records for `root` under `PDD_STATE_DIR` (or `HOME/.pdd/runtime/batches`, filtered by `since` when positive). Never allocate or mutate state. When a saved check report contains multiple `samples` whose step `result`, `error`, `world`, `calls` or check pass states differ—or `rerun.steps` with `changed_paths` or mixed runs—include a concise advisory divergence note naming the step and differing surface. Multi-sample agreement (`k/k samples agreed`) or single-sample runs are noted neutrally. Saved check read failures are ignored safely.

## Compact rendering (`<= 25` lines)

- `formatApproveBoundaryCard(card)` returns at most `25` plain-text lines starting with `Human boundary card (advisory):` and two-space-indented body lines (`Policy:`, `Owner gap:` when unloaded owning sources exist, `Provenance:`, `Verification split:`, `Budget & samples:`). Prioritize `missing owner connection`, `port spy or native observation still needed` and `0 observed port calls` rows before ordinary rows when compacting, and summarize overflow with `… +N more` while always retaining `Verification split:` and `Budget & samples:`. Never start any card line with `Text` or `Approve `.
- `readablePrTop` in [readable workflow PR descriptions](workflow-pr-body.prompt.md) renders `facts.boundary` on PR 1 (`layout: "spec"`) as a `## Boundary` section of at most `25` lines right after `## Summary`, sanitizing all dynamic text as inert Markdown with no forbidden jargon, extra URLs, HTML tags or closing keywords.

## Dependencies

- [Runtime seam](runtime-seam.prompt.md): shared authored-file, Markdown dependency, Story criteria and scenario JSON readers (`readPrompt`, `promptMarkdownTargets`, `storyCriteria`, `parseScenarioJson`, `findTests`, `gitFiles`).
- [Story quality lint](story-lint.prompt.md) and [test selection](test-selection.prompt.md): Story path classification and scenario matching.
