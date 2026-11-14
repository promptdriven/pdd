# Explore active product drafts

Own `src/runtime/product-drafts.mjs`. Export synchronous
`withProductDrafts({root, parts, snapshot, parseProductDocuments, captureSource, readRun}, prepare)`.
It calls `prepare(source, files)` with repository-relative read/stat source ports
and an array of `{path,bytes}` draft inputs, returning the callback result.
The combined source also supplies `validateCapture(sources, capture = {})`, accepting the
final capture's `{path,bytes}` records and its reference/read metadata. After root capture, the client must call
it to refuse any root fallback inside an active draft's owned folder or map,
including references reached only by scenario steps or prompt dependencies.
Also audit reference targets and captured reads: expansion must not hide a root
fallback inside a draft-owned path merely by omitting its raw bytes from upload.
This native source adapter lets `pdd simulate --product` explore connected prompt
space before part code exists or merges. Existing composition owns map assembly,
tap chains, shared world semantics and limits.

## Domain decisions

- Read the product map and optional plan from the product root's attempt snapshot
  using the product parser. Select all parts unless an explicit subset is supplied;
  reject unknown or duplicate parts. Read local workflow run records from this
  checkout's Git common directory. Only active feature runs with the exact
  `<!-- pdd-product: run=RUN -->` marker for a planned run of a selected single
  part qualify. Completed/cancelled runs and `Part: all` do not supply drafts.
  Validate that each draft checkout belongs to the same Git common directory.
  No GitHub lookup, code generation, merge, branch switch or workflow mutation.
  Use the injected host `readRun(runDir)` reader for workflow record parsing;
  the Runtime package imports no host workflow module.
- At most one active run may supply a part, even across slices. Ambiguity refuses
  `invalid-product-map`, naming the part, run IDs and checkout paths. Overlapping
  declared prompt folders also refuse, naming both parts and the conflicting paths.
  Resolve ambiguity in the plan/run records; never select by time or run number.
- A draft supplies its declared Folder, `app/maps/PART.json`, and referenced files
  under `views/` (including stylesheets). Discover linked views with the shared
  Markdown parser, resolving relative to the referring prompt, and follow view
  Markdown links transitively. Include mockup views referenced directly by the map.
  A view claimed by two parts refuses even when its bytes match. A view path that
  overlaps another part's prompt folder or map also refuses.
- Required draft prompts and referenced views must exist and pass the ordinary
  Git visibility, workspace, privacy, symlink and size protections. An active draft
  with no prompt in its Folder refuses. An absent map is allowed for a screenless
  part; if the root has that part's map, absence in its draft refuses. Missing
  draft-owned paths never fall back to root bytes. Errors identify the part and
  authored path and suggest completing or ending the draft.
- Other parts, contracts, plan, journey scenarios and unrelated source stay rooted
  in the product checkout. A draft cannot replace those through a dependency.
  Root shared contracts remain authoritative even if a draft edits its copy.
  With no qualifying drafts, pass the original snapshot and an empty array through.
- Capture each contributing checkout with the existing source-capture attempt
  readers, inside the root preparation attempt. All selected draft inputs must
  remain stable through composition, with the existing bounded capture retry
  policy. Return their raw source bytes as prepared overlay files; final root
  capture owns dependency expansion, schema admission and upload limits. The
  client uses the combined source for composition and tap-cost calculation and
  returns draft inputs with the two generated artifacts and effective seed scenario.
  Never write source files, run records, approvals, branches or worktrees.

## Parser port

`parseProductDocuments({mapText, planText})` is the injected canonical product
parser. Its result supplies `product.parts` records with `part` (part ID) and
`folder` (owned prompt folder), and `product.runs` records with `run` (planned-run
ID) and `part` (part ID or `all`). Preserve its validation and errors; this
adapter does not generate or redefine that parser. The [product owner](product.prompt.md)
is navigation for its wider startup/status responsibilities.

## Dependencies

- [Workflow runs](workflow-runs.prompt.md): required generation context for local
  run records and active/ended state.
- [Preflight](runtime-preflight.prompt.md): required generation context for Git
  visibility and bounded snapshot capture; reuse its source readers.
- [Markdown](runtime-markdown.prompt.md): required generation context for local
  link and image destinations, including reference links.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "reason": "Verifies real Git common-directory/worktree identity and stable source snapshots across multiple checkouts; ordinary Node tests exercise these filesystem and Git boundaries.",
  "status": "approved",
  "prose_sha256": "c2371206fee02ff0495ebe37f9ec59b1bbc04cdd4bee17cd9c041a1336e72b02"
}
```
</details>
