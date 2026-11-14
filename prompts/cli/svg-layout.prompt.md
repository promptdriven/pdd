# SVG layout lint

Own `src/svg-layout.mjs`. Its module function `lintSvgLayouts({root, files, promptPaths})` returns a deterministic array of warning strings for disagreements between screen prompts and their linked `.ui.svg` drawings. It reads local files only, makes no AI or network call and changes no file. Preserve existing Check admission: these warnings never refuse a test or approve a prompt.

`root` is the repository root; `files` is its Git-visible repository-relative file list. With `promptPaths`, inspect those prompts only; without it, inspect every Git-visible `*.prompt.md`. Read local inline and reference-style Markdown image/link destinations ending in `.ui.svg`, relative to their prompt; ignore remote links, fragments and duplicate destinations. Files must stay inside root and be regular files with no symlink ancestors. An unreadable, missing, escaping or malformed drawing produces a warning naming the prompt and drawing; never silently claim it matches.

## Workspace advice

Use the [workspace authority](runtime-workspace.prompt.md) before prompt/drawing content access, including no-Story local scans. Filter optional excluded candidates without opening them; report unavailable advice where relevant. Required linked drawings remain preflight's capture responsibility and cannot be silently pruned. Keep advisory warnings advisory and retain strict no-link reads.


## Parts and advice

The drawing is the layout spec for its declared state: visible parts, words, order and stable ids. Prose owns behavior and dynamic value sources. Ignore Runtime interface JSON, valid comments and SVG `title`, `desc`, `defs`, hidden elements and their descendants. A context-only region, marked `data-context-only="true"` or class `context-only`, and its descendants are outside the owned layout. Decode XML entities and normalize whitespace and case when comparing labels; preserve original spelling in diagnostics. Reject malformed or nested comments with a source/drawing warning; never remove delimiters and reinterpret the result as active markup. CDATA remains literal SVG text. Do not execute SVG scripts or load external resources.

Report all three kinds of disagreement, identifying the prompt, drawing and part:

| Warning | Required observation |
|---|---|
| Prompt control absent from drawing | An explicit control declaration lacks a matching visible drawing part (normalized `id` or `<text>`), reported as `control "<value>": prompt control absent from drawing`. For directional-control phrases (including four direction buttons), check `left`, `right`, `up` and `down` against visible part words and report each missing direction as `move-<direction>` (or the missing group). |
| Drawing label absent from prompt | A visible nonnumeric label is never mentioned in the prompt prose. Match complete normalized words/phrases, not arbitrary substrings. Pure numeric sample values remain dynamic content for this advisory. |
| Drawing region layout unspecified | A visible stable id is not acknowledged as an id/region or named layout part in the prose. Generic data-field mentions do not specify that field's box, bar or container. A label such as SCORE with data prose saying “score” may match as text while the `score` region still needs a layout declaration. |

Explicit control extraction covers both HTML markup and prose while excluding non-control attributes, CSS `.class` tokens and non-control copy:

- **Native HTML controls** (`<button>`, `<input>` with `type` `button`, `submit` or `reset`, `<select>`, `<textarea>`, and other non-`hidden` `<input>` elements, whether written directly or inside Markdown code spans/fences) declare their non-empty `id` and `name`; `<button>` also declares its non-empty `value` and decoded visible text label, and button/submit/reset `<input>` also declares its non-empty `value`. Non-control HTML elements (`<div>`, `<main>`, `<section>`, `<p>`, `<span>`, headings, lists, `<form>`, `<input type="hidden">`, etc.) never declare prompt controls, even when they carry an `id` (such as `<div id="app">` or `<main id="wait-card">`) or sit beside controls.
- **Non-control attributes and CSS selectors** (`class`, `role`, `aria-*`, `data-*`, `style`, `type`, `placeholder`, `title`, `href`, boolean state attributes, `.class` tokens, etc., whether double- or single-quoted or backticked, in HTML markup or prose) never become prompt controls.
- **Prose control declarations** (outside HTML tags) segment sentences and clauses while tracking quote (`"..."`, `'...'`, `“...”`) and Markdown code-span/fence boundaries, so punctuation inside quoted text or code spans (such as multi-sentence help strings) never splits a literal or pairs a closing quote with a subsequent opening quote to capture connecting prose (such as `" Also explain "`). Negated control clauses (`no button`, `no controls`, `without a button`, `without controls`) declare no controls. Affirmative control clauses declare explicit control bindings (`id`, `ids`, `name`, `names`, `value`, `values`), backticked control identifiers tied to the control declaration (excluding HTML snippets, `.class` tokens and non-control field/region identifiers such as `` `instructions` ``), quoted labels tied to the control declaration (excluding attribute values and quoted status, instruction or explanation copy), and directional-control phrases.

Explicit prose or HTML markup such as `region score`, `id="score"`, or “score box” acknowledges the corresponding drawn region without turning non-control container `id`s into required prompt controls. A backticked id within `## Appearance` also acknowledges it. Do not count an interface schema property or a general state-field declaration as a layout mapping. Retain explicit behavioral control declarations anywhere in the prose. Matching is conservative local advice: name uncertain/unmatched parts; do not infer a semantic equivalence or change the prompt/drawing automatically. Report source-read/parse limitations as warnings. This is a vocabulary and part check, not an AI assessment of meaning or a geometry check.

## Domain decisions: controls in multiple views

For one distinct linked drawing, keep whole-prompt control extraction unchanged. With multiple drawings, require shared controls on every drawing, but require view-specific controls only on the drawings associated with their Markdown section, list item (including indented children), or interleaved labeled view block. A section ends at a sibling/ancestor heading, a list item at its sibling or dedent, and a labeled block at the next label or enclosing boundary. Controls before, between and after those scopes remain shared within their enclosing scope.

Associate a scope with its explicit local drawing links (inline or reference-style, including links after the controls). A section may contain multiple drawings for one view; its controls apply to all of them. A narrower child association overrides its enclosing view. Reference definitions alone do not start a view scope. Without a local link, a heading or leading label may identify the drawing's filename state (`<state>` in `views/<state>[--<variant>]__<layout-mode>.ui.svg`) or its complete filename stem; match whole names ignoring case, Markdown emphasis and hyphen/underscore spacing. A state applies to all its variants/layouts. Incidental mentions in navigation or control sentences do not start view scopes. Unassociated prose remains shared; never use the controls present in a drawing to decide which requirements apply. Markdown examples inside fenced code do not create scope boundaries, while their actual controls remain subject to the existing extraction rules.

Only prompt-to-drawing control requirements are scoped. Drawing-to-prompt label and region checks, safety/read diagnostics, warning ordering/deduplication, and advisory admission remain unchanged. This avoids cross-view false positives without hiding shared or own-view omissions.

Also inspect workspace-allowed `prompt-runtime.app-map.v1` app maps (`(^|/)app-map\.json$` in `files` plus string entries of `"app_maps"` in workspace-allowed `test/**/*.json` and `tests/**/*.json` files) and delegate stylesheet and CSS-class checks for inspected prompts to [screen design check](screen-design-check.prompt.md). Read each referenced stylesheet safely inside `root` without following symlinks, passing any read/escape/symlink failure as that stylesheet's `error` record rather than throwing. Merge its returned warnings into the deduplicated sorted output.

Warnings start `Warning: SVG layout`, are deduplicated and ordered by prompt path, drawing path and part. A 2048-like screen with four direction buttons only in prose and SCORE/SEED boxes and a READY bar only in the drawing must warn about directions, READY and the unspecified score/seed layout regions, even when prose mentions score and seed data.

## Dependencies

- [Workspace authority](runtime-workspace.prompt.md): required generation/runtime/verification context for opt-in permission.
- [Screen design check](screen-design-check.prompt.md): required generation/runtime/verification context for HTML screen stylesheet and CSS-class warnings.

- [Screen rules](../../skills/pdd-prompting/runbook/screens-and-svg.md#13-give-your-app-a-screen-app-map): authoring and verification context.

## Caller navigation

The CLI exposes this advisory through [Check](runtime-client.prompt.md).

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "approved",
  "prose_sha256": "b7b5e93d123e371b4ea38cdf47b8066c905caca09a16752ab84d955a4311cda7",
  "reason": "lintSvgLayouts reads real local prompt/drawing files and checks regular-file and symlink ancestors through its native filesystem boundary; it has no injectable file port. Native tests exercise its deterministic view policy and the public local-lint command alongside these reads."
}
```
</details>
