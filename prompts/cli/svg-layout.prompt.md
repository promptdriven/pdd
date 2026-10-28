# SVG layout lint

Own `src/svg-layout.mjs`. Its module function `lintSvgLayouts({root, files, promptPaths})` returns a deterministic array of warning strings for disagreements between screen prompts and their linked `.ui.svg` drawings. It reads local files only, makes no AI or network call and changes no file. Preserve existing Check admission: these warnings never refuse a test or approve a prompt.

`root` is the repository root; `files` is its Git-visible repository-relative file list. With `promptPaths`, inspect those prompts only; without it, inspect every Git-visible `*.prompt.md`. Read local inline and reference-style Markdown image/link destinations ending in `.ui.svg`, relative to their prompt; ignore remote links, fragments and duplicate destinations. Files must stay inside root and be regular files with no symlink ancestors. An unreadable, missing, escaping or malformed drawing produces a warning naming the prompt and drawing; never silently claim it matches.

## Parts and advice

The drawing is the layout spec for its declared state: visible parts, words, order and stable ids. Prose owns behavior and dynamic value sources. Ignore Runtime interface JSON, comments and SVG `title`, `desc`, `defs`, hidden elements and their descendants. A context-only region, marked `data-context-only="true"` or class `context-only`, and its descendants are outside the owned layout. Decode XML entities and normalize whitespace and case when comparing labels; preserve original spelling in diagnostics. Do not execute SVG scripts or load external resources.

Report all three kinds of disagreement, identifying the prompt, drawing and part:

| Warning | Required observation |
|---|---|
| Prompt control absent from drawing | A control explicitly named by id, quoted label, or a directional-control phrase (including four direction buttons) lacks a matching visible drawing part. For directional controls name each missing direction or the missing group. |
| Drawing label absent from prompt | A visible nonnumeric label is never mentioned in the prompt prose. Match complete normalized words/phrases, not arbitrary substrings. Pure numeric sample values remain dynamic content for this advisory. |
| Drawing region layout unspecified | A visible stable id is not acknowledged as an id/region or named layout part in the prose. Generic data-field mentions do not specify that field's box, bar or container. A label such as SCORE with data prose saying “score” may match as text while the `score` region still needs a layout declaration. |

Explicit prose such as `region score`, `id="score"`, or “score box” acknowledges the corresponding named region. A backticked id within `## Appearance` also acknowledges it. Do not count an interface schema property or a general state-field declaration as a layout mapping. Retain explicit behavioral control-id declarations anywhere in the prose. Matching is conservative local advice: name uncertain/unmatched parts; do not infer a semantic equivalence or change the prompt/drawing automatically. Report source-read/parse limitations as warnings. This is a vocabulary and part check, not an AI assessment of meaning or a geometry check.

Warnings start `Warning: SVG layout`, are deduplicated and ordered by prompt path, drawing path and part. A 2048-like screen with four direction buttons only in prose and SCORE/SEED boxes and a READY bar only in the drawing must warn about directions, READY and the unspecified score/seed layout regions, even when prose mentions score and seed data.

## Dependencies

- [Screen rules](../../RUNBOOK.md#13-give-your-app-a-screen-app-map): authoring and verification context; the CLI exposes this advisory through [Check](runtime-client.prompt.md).
