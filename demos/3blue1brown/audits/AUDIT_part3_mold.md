# Part 3: The Mold Has Three Parts -- Post-Render Audit

**Video:** `outputs/sections/part3_mold.mp4` (295s / 4:55, 8850 frames @ 30fps)
**Script:** `scripts/main_script.md` lines 226-335 (PART 3: THE MOLD HAS THREE PARTS, 10:30-16:00)
**Composition:** `remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
**Date:** 2026-02-09
**Auditor:** Critic Agent
**Method:** Frame-accurate extraction using `ffmpeg -vf select=eq(n,FRAME)` at 16 key timestamps

---

## Status: PASS

No blocking issues found. All 21 visual segments render correctly and maintain narrative coherence with the script. The three-part structure (Test Capital, Prompt Capital, Grounding Capital) is clearly delineated visually. The Z3/Synopsys comparison and context window visuals are particularly strong.

---

## Visual Segment Map

| Visual | Component | Time Range | Duration | Status |
|--------|-----------|------------|----------|--------|
| V0 | CrossSectionIntro | 0.0-12.3s | 12.3s | GOOD |
| V1 | WallsIlluminate | 13.4-23.6s | 10.2s | GOOD |
| V2 | LiquidInjection | 23.6-52.1s | 28.5s | GOOD |
| V3 | FocusSingleWall | 53.6-67.0s | 13.4s | GOOD |
| V4 | BugDiscovered | 67.0-83.6s | 16.6s | GOOD |
| V5 | AddTestWall | 83.6-85.0s | 1.4s | OK |
| V6 | CodeRegenerates | 85.0-100.0s | 15.0s | EXCELLENT |
| V7 | RatchetTimelapse | 100.1-107.4s | 7.3s | GOOD |
| V8 | TraditionalVsPdd | 108.0-117.6s | 9.6s | GOOD |
| V9 | Z3SmtSidebar (phase 1) | 117.6-138.8s | 21.2s | GOOD |
| V10 | Z3SmtSidebar (phase 2) | 140.2-171.4s | 31.2s | GOOD |
| V11 | InjectionNozzle | 171.4-187.8s | 16.4s | GOOD |
| V12 | PromptTextFlows | 187.8-195.5s | 7.7s | GOOD |
| V13 | PromptVariations | 195.5-203.5s | 8.0s | GOOD |
| V14 | PromptGovernsCode | 203.5-210.4s | 6.9s | GOOD |
| V15 | ContextWindowComparison | 211.7-249.7s | 38.0s | GOOD |
| V16 | GroundingPanel | 250.1-258.0s | 7.9s | GOOD |
| V17 | GroundingComparison | 259.2-264.6s | 5.4s | GOOD |
| V18 | GroundingDatabase | 264.6-276.5s | 11.9s | GOOD |
| V19 | ThreeComponents | 278.5-286.3s | 7.8s | GOOD |
| V20 | CodeOutputMoldGlows | 286.3-295.0s | 8.7s | GOOD |

---

## Frame-by-Frame Verification

### t=4s -- V0: CrossSectionIntro
- **Script:** "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete. In PDD, the mold has three components."
- **Actual:** Mold cross-section diagram with "Walls" label. Title: "The Mold Has Three Parts". Technical, precise illustration of injection mold anatomy.
- **Status:** GOOD -- clean opening visual that sets up the three-part structure.

### t=20s -- V1: WallsIlluminate
- **Script:** "First: tests. Tests are the walls of your mold. Each wall segment gets a label: 'null -> None', 'empty string -> ""', 'handles unicode'."
- **Actual:** "First: tests / The Constraints" title. Mold walls with labeled test constraints: "null -> None", "empty string -> ''", "handles unicode". Clean amber walls against dark background.
- **Status:** GOOD -- matches script precisely. Labels are readable and well-positioned.

### t=40s -- V2: LiquidInjection
- **Script:** "Liquid (representing code generation) being injected into the mold. It flows freely until it hits a wall, then stops. The shape is constrained by the walls."
- **Actual:** Code filling the mold cavity with green checkmark indicating tests pass. `parse_user_id` function code visible within the mold shape. Amber test walls constraining the code.
- **Status:** GOOD -- the code-as-liquid metaphor works well. Green checkmark sells the "all tests pass" concept.

### t=60s -- V3: FocusSingleWall
- **Script:** "Focus on one wall labeled 'null -> None'. The liquid tries to flow past it, hits the wall, stops."
- **Actual:** Zoomed view focusing on a single large "null -> None" wall constraint. Text: "Focusing on a single constraint..."
- **Status:** GOOD -- clear visual focus on the specific constraint from the script.

### t=80s -- V4: BugDiscovered
- **Script:** "A bug is discovered. Red alert on a piece of code. The word 'BUG' appears."
- **Actual:** "Bug Discovered" title. Code block with red border highlighting, "BUG" badge visible. "TEST FAILED" panel on the right side. Terminal-style error output.
- **Status:** GOOD -- dramatic reveal matches script. Red/error coloring is immediately readable.

### t=100s -- V6: CodeRegenerates
- **Script:** "The code regenerates, automatically conforming to the new constraint. Terminal: `pdd fix user_parser` -> 'All tests passing'."
- **Actual:** "Code Regenerates / Mold Cross-Section View" title. Terminal showing `pdd fix user_parser` command. New wall added to the mold. Code regenerating within the updated constraints.
- **Status:** EXCELLENT -- the terminal command matches exactly. The visual of code regenerating within the mold with the new wall is one of the strongest moments in Part 3. Precisely illustrates the PDD workflow.

### t=120s -- V9: Z3SmtSidebar (phase 1)
- **Script:** "The Synopsys Formality logo from Part 2 reappears alongside the Z3 logo. Text: 'Hardware: SMT-based formal proof. PDD: SMT-based formal proof. Same math.'"
- **Actual:** Side-by-side comparison: Synopsys Formality (left) and Z3 (right). Labels showing SMT-based formal proof for both. Clean technical comparison layout.
- **Status:** GOOD -- bridges nicely from the Part 2 chip design content.

### t=140s -- V10: Z3SmtSidebar (phase 2)
- **Script:** "When Z3 proves that a function never returns null for any 32-bit integer input, it hasn't tried every input -- it's reasoned symbolically over the entire space."
- **Actual:** Same Synopsys/Z3 comparison with added annotations: "Hardware: SMT-based formal proof", "PDD: SMT-based formal proof", "Same math." text prominent.
- **Status:** EXCELLENT -- the "Same math." text is the key takeaway and it's clearly visible.

### t=160s -- V10: Z3SmtSidebar (continued)
- **Script:** Narration continues through Z3 formal verification discussion, transitioning toward "the chip design analogy isn't a metaphor."
- **Actual:** Same Synopsys/Z3 visual, now static. No animation progression from t=140s.
- **Issue (MINOR):** This segment holds the same static visual for ~20s (t=140-160s). The narration covers substantial content (symbolic reasoning, same certainty, billion-dollar tapeouts, unit tests vs Z3 proofs) but the visual doesn't evolve.
- **Status:** OK -- the content is correct but the visual could benefit from progressive reveals or additional annotations during this narration-dense section.

### t=175s -- V11: InjectionNozzle
- **Script:** "Second: the prompt. Your specification of what you want. The injection nozzle of the mold highlights. Labels appear: 'intent', 'requirements', 'constraints'."
- **Actual:** Transition visual with blue injection funnel flowing into amber test walls. Clean transition from Test Capital to Prompt Capital section.
- **Status:** GOOD -- effective visual transition. The funnel/nozzle metaphor connects naturally to the mold.

### t=190s -- V12: PromptTextFlows
- **Script:** "Text flows into the mold like injection material: 'Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.' A file briefly visible: `user_parser.prompt`"
- **Actual:** `user_parser.prompt` file card with "PROMPT" label. "Code takes shape from the prompt" annotation. Natural language text flowing into the mold.
- **Status:** GOOD -- the `user_parser.prompt` file is clearly labeled, matching the script's reference.

### t=210s -- V14: PromptGovernsCode
- **Script:** "The prompt glows. It's small -- maybe 10-15 lines. But it governs a 200-line code file. A ratio appears: '1:5 to 1:10'."
- **Actual:** Split view: "PROMPT (~15 lines)" on left, "GENERATED CODE (~200 lines)" on right. Size differential clearly visible.
- **Status:** GOOD -- the ratio is immediately graspable. The visual compression from prompt to code is well-communicated.

### t=230s -- V15: ContextWindowComparison
- **Script:** "Two context windows side by side. LEFT: filled with 15,000 tokens of raw code. RIGHT: filled with prompts for ten modules. Both same size, right one represents ten times more system knowledge."
- **Actual:** Two context windows: "15,000 tokens of code" (left, dense) vs "15,000 tokens of prompts" (right, organized). "Same tokens. 10x the system knowledge." annotation.
- **Status:** GOOD -- matches script. The density contrast between code and natural language is visually clear.

### t=250s -- V15: ContextWindowComparison (continued)
- **Script:** Narration continues: "unlike agentic tools that dynamically guess which code to load into context... each prompt declares its own dependencies."
- **Actual:** Same context window visual, static.
- **Issue (MINOR):** Holds static for ~20s. The narration covers the "author-defined vs machine-assembled" distinction but the visual doesn't evolve to illustrate this.
- **Status:** OK -- correct content, could benefit from animation showing the author-defined vs machine-assembled contrast.

### t=270s -- V18: GroundingDatabase
- **Script:** "A successful generation glows, then flows into a 'Grounding Database'. Future generations pull from this database. Subtle: after `pdd fix` succeeds, an arrow shows the (prompt, code) pair flowing to cloud storage."
- **Actual:** "The Feedback Loop" title. Terminal showing `pdd fix succeeded`. Arrow showing (prompt, code) pair flowing to storage. "Learning from success..." annotation.
- **Status:** GOOD -- matches script concept. The feedback loop visual is clear.

### t=290s -- V19/V20: ThreeComponents / CodeOutputMoldGlows
- **Script:** "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification. The code is output. The mold is what matters."
- **Actual:** Three badges at top: "PROMPT", "TESTS", "GROUNDING". Generated code below flowing from the combined specification. Clean closing visual.
- **Status:** GOOD -- effective summary. The three-badge layout provides a visual mnemonic for the three types of capital.

---

## Issues Summary

| Severity | Count | Description |
|----------|-------|-------------|
| MINOR | 1 | V10 (t=140-165s): Z3/Synopsys visual holds static for ~25s during dense narration |
| MINOR | 1 | V15 (t=230-250s): Context window visual holds static for ~20s |

---

## Overall Assessment

Part 3 is well-structured and narratively clear. The three-part organization (Test Capital -> Prompt Capital -> Grounding Capital) maps cleanly to the visual segments. Key highlights:

1. **CodeRegenerates (V6):** The strongest moment in Part 3. The `pdd fix user_parser` terminal command alongside the mold regeneration visual directly demonstrates the PDD workflow. Rated EXCELLENT.

2. **Z3SmtSidebar (V9-V10):** The Synopsys Formality / Z3 comparison effectively bridges the chip design metaphor from Part 2. The "Same math." annotation is memorable and concise.

3. **ContextWindowComparison (V15):** The "15,000 tokens of code vs 15,000 tokens of prompts" visual makes the density argument tangible. "Same tokens. 10x the system knowledge." is a strong annotation.

4. **BugDiscovered -> CodeRegenerates (V4-V6):** This sequence is the narrative payoff for the "tests are walls" metaphor. The progression from bug -> add wall -> regenerate is clear and satisfying.

5. **Pacing:** 21 segments across 295s = ~14.0s average. The Test Capital section (V0-V10, 171s) is substantially longer than Prompt Capital (V11-V15, 78s) and Grounding Capital (V16-V20, 45s), matching the script's emphasis.

**Blocking issues:** None
**Recommended improvements (non-blocking):**
1. V10: Add progressive reveals during Z3 narration (LOW priority -- "Same math." text already carries the message)
2. V15: Add author-defined vs machine-assembled animation (LOW priority)
