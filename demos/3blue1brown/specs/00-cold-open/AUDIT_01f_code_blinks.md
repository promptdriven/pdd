# Audit: 01f_code_blinks.md

## Status: ISSUES FOUND

### Requirements Met

1. **Dark background color**: The spec requires `#1E1E2E` background. VISUAL_03 in `ColdOpenSection.tsx` (line 75) uses `backgroundColor: "#1a1a2e"` on the outer fill and `background: "#1E1E2E"` (line 85) on the code block itself. The code block matches spec; the outer container is close but slightly different (`#1a1a2e` vs `#1E1E2E`).

2. **Python patched function code content**: The spec provides a `parse_user_input` function with inline patch comments. VISUAL_03 (line 86) renders a Python function named `parse_user_input` with similar patch-style comments (`# patched: handle None input (hotfix 2024-01)`, `# workaround for unicode edge case`, `# TODO: this whole block needs refactoring`, `# don't remove -- breaks downstream`). The code content is a reasonable match to the spec's code sample.

3. **JetBrains Mono font**: VISUAL_03 (line 86) uses `fontFamily: "'JetBrains Mono', monospace"`, matching the spec's font requirement.

4. **1920x1080 resolution**: `S00-ColdOpen/constants.ts` (lines 18-19) defines `COLD_OPEN_WIDTH = 1920` and `COLD_OPEN_HEIGHT = 1080`, matching spec.

### Issues Found

#### Issue 1: Beat merged with 01g code regeneration -- not a standalone scene
- **Spec says**: Section 0.6 "Code Blinks" is a standalone ~10-second contemplative beat (timestamp 1:25-1:35) where patched code sits static on screen with only a blinking cursor for motion. It is followed by a hard cut to Section 0.7 (01g) where the function deletes and regenerates clean.
- **Implementation does**: VISUAL_03 in `ColdOpenSection.tsx` (lines 73-115) combines both beats into a single ~1-second sequence (frames 383-413 at 30fps = ~1 second). The old patched code immediately begins dissolving (blur + fade at frames 10-25 local) while new clean code fades in (frames 18-30 local). There is no standalone "code blinks" hold.
- **Impact**: High. The spec's entire emotional purpose -- a contemplative pause where the viewer absorbs accumulated technical debt -- is absent. The ~6-8 second static hold that defines this beat does not exist.
- **Spec ref**: Animation Sequence steps 2-4 (frames 15-300), "breathing room" shot description.
- **Code ref**: `S00-ColdOpen/ColdOpenSection.tsx` lines 73-115, `S00-ColdOpen/constants.ts` lines 37-39 (VISUAL_03: frames 383-413).

#### Issue 2: No blinking cursor animation
- **Spec says**: Standard block cursor, white `#FFFFFF`, blinks at ~530ms interval (on for 16 frames, off for 16 frames at 30fps), positioned at end of a complex line deep in the function. "The cursor blink is the only motion -- everything else is static."
- **Implementation does**: No cursor element exists anywhere in `ColdOpenSection.tsx`. The code is rendered as a static `<pre>` block with no interactive or animated cursor element.
- **Impact**: High. The blinking cursor is the defining visual motif of this beat -- "one small point of motion in a dense, static scene."
- **Spec ref**: Animation Elements item 3 (Blinking Cursor), Code Structure lines 130-133 and 175-181.
- **Code ref**: `S00-ColdOpen/ColdOpenSection.tsx` lines 85-87 (static pre block, no cursor).

#### Issue 3: No patch layer color coding by era
- **Spec says**: Multiple patch layers with distinct color temperatures showing different "eras" of modifications: original code `#C0C0C0`, first patch `#C4A8A0`, second patch `#C89890`, third patch `#CC8880`. Lines should be visually distinguishable by their age/era through warming color progression.
- **Implementation does**: All code text is rendered in a single color `#8a9caf` (line 86). No per-line or per-section color differentiation exists. The code appears monochrome.
- **Impact**: Medium. The "geological strata" visual metaphor that communicates accumulated technical debt layering is absent.
- **Spec ref**: Animation Elements item 2 (Complex Patched Function, color coding), Code Structure lines 154-159 (patchLayers).
- **Code ref**: `S00-ColdOpen/ColdOpenSection.tsx` line 86 (`color: "#8a9caf"`).

#### Issue 4: No git-blame style gutter indicators
- **Spec says**: Faint colored bars in the gutter (git-blame style) with 4-5 distinct muted color bands (`#3A4A5A`, `#4A3A3A`, `#4A4A3A`, `#5A3A3A`, `#3A3A4A`) showing different eras of patches. Also a small yellow warning triangle icon next to one comment line.
- **Implementation does**: No gutter element, no blame-style colored bars, no warning icon. The code block has no side decorations.
- **Impact**: Medium. These elements reinforce the visual narrative of code evolving through many hands and patches.
- **Spec ref**: Animation Elements item 4 (Subtle Patch Indicators), Code Structure lines 164-172 (BlameGutter) and line 184 (WarningIcon).
- **Code ref**: `S00-ColdOpen/ColdOpenSection.tsx` lines 85-87 (bare code block, no gutter).

#### Issue 5: No editor chrome (title bar, line numbers)
- **Spec says**: Full-screen dark code editor with VS Code/Cursor aesthetic. Includes a subtle top bar with filename `user_parser.py`, line numbers in gutter (muted gray `#555`), minimal editor chrome.
- **Implementation does**: The code is inside a plain `<div>` with `background: "#1E1E2E"`, padding, border-radius, and a red border (`border: "1px solid #E74C3C"`). No title bar, no line numbers, no editor chrome. The red border is not specified anywhere in the spec and contradicts the minimal aesthetic.
- **Impact**: Medium. The editor mockup communicates "this is a real codebase" and the filename grounds the viewer in a specific file.
- **Spec ref**: Animation Elements item 1 (Code Editor Frame), Code Structure lines 146-149.
- **Code ref**: `S00-ColdOpen/ColdOpenSection.tsx` line 85.

#### Issue 6: No fade-in from previous scene
- **Spec says**: Frame 0-15 (0-0.5s): Fade in from black with `easeOutCubic` opacity transition.
- **Implementation does**: VISUAL_03 starts immediately at full opacity. The old patched code is at opacity 1 from frame 0 of the local sequence (line 82: opacity interpolation starts `[0, 10, 11, 25]` mapping to `[1, 1, 1, 0]` -- starts at full opacity).
- **Impact**: Low. The transition approach is different but may not be noticeable in context since VISUAL_02 (a Veo clip) precedes it.
- **Spec ref**: Animation Sequence step 1 (frames 0-15).
- **Code ref**: `S00-ColdOpen/ColdOpenSection.tsx` line 82.

#### Issue 7: No vignette darkening effect
- **Spec says**: Frame 240-300 (8-10s): Slight vignette darkening at edges, subtle 5% opacity.
- **Implementation does**: No vignette overlay in VISUAL_03. Since the beat is only ~1 second, there is no time window for a vignette anyway.
- **Impact**: Low. Atmospheric detail; depends on the static hold existing at all (Issue 1).
- **Spec ref**: Animation Sequence step 4 (frames 240-300), Code Structure lines 136-141.
- **Code ref**: Not present in `ColdOpenSection.tsx`.

#### Issue 8: Duration mismatch (~1s vs ~10s)
- **Spec says**: ~10 seconds duration (300 frames at 30fps). Timestamp 1:25-1:35.
- **Implementation does**: VISUAL_03 spans frames 383-413 = 30 frames at 30fps = ~1 second. Furthermore, the spec timestamp of 1:25 (85 seconds) is far beyond the implemented cold open total duration of 19 seconds.
- **Impact**: High. The beat is 10x shorter than specified. The entire cold open section was significantly restructured from the original spec timing.
- **Spec ref**: Duration header, Animation Sequence timing.
- **Code ref**: `S00-ColdOpen/constants.ts` lines 37-39.

#### Issue 9: "01f" label reused for different visual
- **Spec says**: 01f refers to "Code Blinks" -- static patched code with blinking cursor.
- **Implementation does**: In `S00-ColdOpen/constants.ts` line 33, VISUAL_02 references `veo:cold_open_01f_modern_sock_toss`, which is a Veo video clip of modern sock tossing aligned to the narration "60 years ago, when socks got cheap enough, she stopped." The `01f` label in the implementation refers to a completely different visual than the spec.
- **Impact**: Medium. Namespace confusion -- the same section identifier maps to unrelated content between spec and implementation.
- **Code ref**: `S00-ColdOpen/constants.ts` lines 33-34, `ColdOpenSection.tsx` line 65.

### Notes

The spec describes a contemplative "breathing room" shot -- a full 10-second static hold where the viewer absorbs the weight of accumulated technical debt through a densely-patched function, with only a lonely blinking cursor for motion. This is followed by a hard cut to 01g where the function regenerates clean. The emotional payload depends on the contrast between the two beats.

The implementation takes a fundamentally different architectural approach. The cold open section (`S00-ColdOpen`) uses Veo-generated video clips for most visuals and compresses the entire narrative into ~19 seconds. The "code blinks" concept is not implemented as a standalone beat. Instead, VISUAL_03 performs a quick ~1-second dissolve from patched code to clean code, effectively merging specs 01f and 01g into a single rapid transition.

The `01-ColdOpen` directory contains a separate split-screen Remotion implementation (developer/code on left, grandmother/darning on right) which is a different concept from the S00-ColdOpen section that uses Veo clips. Neither implementation contains the standalone CodeBlinks beat.

No standalone `CodeBlinks` component exists anywhere in the Remotion source. The components specified in the spec's code structure (`EditorTopBar`, `LineNumberGutter`, `BlameGutter`, `WarningIcon`, `Cursor`, `Vignette`, `CodeBlock`) have not been created.

The patched code content in VISUAL_03 (line 86) does include the correct function name and most of the specified inline comments, so the textual content is partially aligned even though the visual presentation diverges significantly from spec.
