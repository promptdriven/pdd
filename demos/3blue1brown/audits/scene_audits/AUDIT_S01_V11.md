# Scene Audit: S01 V11 - ContextRot (context window appears)

**Section:** S01 Part 1 Economics
**Scene:** V11 - ContextRot (context window appears)
**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 148.4s - 159.62s (11.22s duration)
**Remotion component:** `remotion/src/remotion/07-ContextRot/` (specifically `ContextWindowVisualization.tsx` and `DebtLayerSeparation.tsx`)
**Audit date:** 2026-02-09

---

## Script Requirements

**Visual description:** "The chart morphs into a new visualization. A glowing rectangular 'context window' appears over a small codebase represented as a 4x4 grid of code blocks. The window covers most of the grid (~80%)."

**Narration:** "When your codebase is small, AI tools are brilliant. The context window -- what the model can actually see -- covers almost everything. It understands how the pieces connect."

---

## Frame-by-Frame Analysis

### Internal Timing Mapping

V11 spans Part1Economics frames 4452-4789. The ContextRot component is mounted with `<Sequence from={-240}>`, yielding internal ContextRot frames 240-577. Key ContextRot beats during this window:

| ContextRot Beat | Frame | Mapped V11 Time |
|---|---|---|
| HOLD_LAYERS (Part 1 ending) | 240-300 | ~148.4s - 150.4s |
| MORPH_TO_GRID_START | 300 | ~150.4s |
| MORPH_TO_GRID_END | 360 | ~152.4s |
| SMALL_CODEBASE_START | 360 | ~152.4s |
| CODEBASE_GROWTH_START | 540 | ~158.4s |

### Frame 1: t=149s (ContextRot frame ~270)

**Observed:** The screen shows the "Context Rot: The AI-Specific Problem" debt layer chart with two labeled bands -- "Context Rot" (upper, lighter amber) and "Code Complexity" (lower, darker amber). This is the DebtLayerSeparation component still visible as part1Opacity fades from 1 toward 0.

**Expected per script:** The chart should be "morphing into a new visualization" at this point.

**Assessment:** ACCEPTABLE. At ContextRot frame 270, the debt layer chart from V10 is still fading out (part1Opacity transitions [240, 300] -> [1, 0]). The morph to grid begins at frame 300 (~150.4s). The fade-out of the previous chart IS the beginning of the morph transition. By t=150s the grid starts appearing. This is a smooth visual transition, not a hard cut.

### Frame 2: t=154s (ContextRot frame ~408)

**Observed:** The screen displays:
- Title: "The Shrinking Context Window" (top center)
- A 4x4 grid of code blocks (16 dark purple/blue blocks with subtle code-line indicators)
- A glowing blue rectangular context window overlaying most of the grid
- "Context Coverage 80%" counter (top right, with blue highlight)
- "Codebase: 4x4 modules (16 total)" label (bottom left)
- "Small project - AI sees almost everything" text (bottom center, green-tinted)

**Expected per script:** "A glowing rectangular 'context window' appears over a small codebase represented as a 4x4 grid of code blocks. The window covers most of the grid (~80%)."

**Assessment:** PASS. This frame is an excellent match to the spec:
- 4x4 grid of code blocks: present and clearly rendered
- Glowing rectangular context window: visible with blue glow effect
- ~80% coverage: explicitly shown as "80%" in the counter
- The label "Small project - AI sees almost everything" directly reinforces the narration

### Frame 3: t=159s (ContextRot frame ~558)

**Observed:** The screen shows:
- Title: "The Shrinking Context Window" (top center)
- The same 4x4 grid of code blocks, but some blocks near the edges are now outside the context window
- Context window still visible with blue glow but not covering the full grid
- "Context Coverage 68%" (dropping from 80%)
- "Codebase: 4x4 modules (16 total)" label (bottom left)
- No state label text visible

**Expected per script:** The scene should still show the small codebase with high coverage. The narration at this point (~159s) says "It understands how the pieces connect."

**Assessment:** MINOR CONCERN. At ContextRot frame 558, the codebase growth animation has begun (CODEBASE_GROWTH_START = 540). The coverage counter shows 68%, already a noticeable drop from the script's stated ~80%. However, since the scene transitions to V12 at 159.62s (which covers "codebases grow"), this early start of the growth animation provides a smooth visual lead-in. The growth is subtle at this point -- the grid still appears as 4x4 and the coverage drop is gradual.

---

## Verdict: PASS

### Summary

The scene successfully conveys the key visual concept described in the script. The central frame (t=154s) is a near-perfect match: a 4x4 grid of code blocks with a glowing blue context window covering 80% of the grid, exactly as specified. The supporting UI elements (coverage counter, grid size label, state description) reinforce the narration clearly.

### Minor Notes

1. **Transition at scene start (t=149s):** The first ~2 seconds show the previous visualization (debt layers) fading out before the grid appears. This is an intentional cross-fade transition, not a visual error.

2. **Early growth at scene end (t=159s):** The codebase growth animation begins at ContextRot frame 540 (~158.4s), causing coverage to start dropping to 68% by t=159s. This is ~1.2 seconds before the V12 scene boundary. The early start creates smoother visual continuity into the next scene but means the "small codebase" message is slightly undermined at the very end of V11. This is a minor timing subtlety, not a functional issue.

3. **Title reads "The Shrinking Context Window"** rather than anything about "Context Rot" -- this is appropriate since the ContextWindowVisualization sub-component uses its own title during Part 2, and the "Context Rot" title only appears during Part 1 (debt layers) and Part 3 (return to chart).
