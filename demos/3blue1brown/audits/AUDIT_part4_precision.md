# Part 4: The Precision Tradeoff -- Post-Render Audit

**Video:** `outputs/sections/part4_precision.mp4` (61s / 1:01, 1830 frames @ 30fps)
**Script:** `narrative/main_script.md` lines 335-374 (PART 4: THE PRECISION TRADEOFF, 16:00-18:00)
**Composition:** `remotion/src/remotion/S04-PrecisionTradeoff/Part4PrecisionTradeoff.tsx`
**Date:** 2026-02-09
**Auditor:** Critic Agent
**Method:** Frame-accurate extraction using `ffmpeg -vf select=eq(n,FRAME)` at 10 key timestamps

---

## Status: PASS

No blocking issues found. All 8 visual segments render correctly and deliver the precision tradeoff argument clearly. The narrative arc from 3D printing through injection molding to the inverse curve is well-paced. The `parser_v1.prompt` (50 lines) vs `parser_v2.prompt` (10 lines) comparison is the visual centerpiece and matches the script precisely.

---

## Visual Segment Map

| Visual | Component | Time Range | Duration | Status |
|--------|-----------|------------|----------|--------|
| V0 | Veo: split 3D vs mold | 0.0-3.0s | 3.0s | GOOD |
| V1 | PrinterFocus | 4.4-14.5s | 10.1s | GOOD |
| V2 | MoldFlowFocus | 15.7-22.1s | 6.4s | GOOD |
| V3 | PrecisionGraph | 23.4-25.8s | 2.4s | GOOD |
| V4 | LongPrompt | 26.7-34.6s | 7.9s | GOOD |
| V5 | ShortPromptTests | 35.3-42.0s | 6.7s | GOOD |
| V6 | GraphAnimateCurve | 43.1-52.0s | 8.9s | EXCELLENT |
| V7 | BothGenerateFinal | 52.8-58.6s | 5.8s | GOOD |

---

## Frame-by-Frame Verification

### t=1s -- V0: Veo split 3D printing vs molding
- **Script:** "Split screen. LEFT: A 3D printer depositing material precisely, layer by layer. RIGHT: Injection mold with liquid flowing until it hits walls."
- **Actual:** Split screen. LEFT: 3D printer extruder head with dark material depositing. RIGHT: Injection mold with orange plastic flowing into shaped cavity.
- **Status:** GOOD -- clean split-screen opening. Both manufacturing processes clearly distinguishable.

### t=7s -- V1: PrinterFocus
- **Script:** "Focus on 3D printer. Highlight how every single point must be specified. A coordinate grid appears, showing the precision required."
- **Actual:** Close-up of 3D printer extruder head printing a blue circular part. "3D PRINTER COORDINATE SYSTEM" title at top. X, Y, Z axis labels visible on the coordinate system overlay.
- **Status:** GOOD -- coordinate system overlay effectively shows the point-by-point precision requirement.

### t=12s -- V1: PrinterFocus (continued)
- **Script:** "The specification must be extremely precise."
- **Actual:** Same 3D printer view with coordinate system. Now includes POSITION readout panel (top-right): "X: 127.2, Y: 53.3, Z: 24.0". Crosshair cursor on the printer.
- **Status:** GOOD -- the real-time position readout reinforces "every single point must be specified." The crosshair and coordinate display are technically accurate.

### t=18s -- V2: MoldFlowFocus
- **Script:** "In injection molding, precision comes from the walls. The material just flows until it's constrained."
- **Actual:** Stunning Veo clip of transparent injection mold cross-section. Bright red/orange liquid plastic flowing into the mold cavity. Metal walls constraining the flow. "Injection Mold Cross-Section" label visible at top.
- **Status:** GOOD -- one of the best Veo clips in the production. The transparent mold showing liquid being constrained by walls is exactly the visual metaphor the script needs.

### t=25s -- V3: PrecisionGraph (early)
- **Script:** "Graph appears. X-axis: 'Number of Tests'. Y-axis: 'Required Prompt Precision'. An inverse curve forms."
- **Actual:** Bare X/Y axes appearing (animation just starting). At t=26s: labels "Required Prompt Precision" (Y), "Number of Tests" (X), "FEW TESTS" (upper left), "MANY TESTS" (lower right) fade in.
- **Status:** GOOD -- V3 is only 2.4s; it sets up the graph frame before the concrete examples (V4-V5). The curve draws later in V6.

### t=30s -- V4: LongPrompt
- **Script:** "A long, detailed prompt appears. Dense with requirements. File: `parser_v1.prompt` - 50 lines."
- **Actual:** `parser_v1.prompt` card with "50 lines" badge. Content sections visible: "## Input Handling" (Accept string input, Handle null/undefined, Handle empty strings, Handle whitespace-only, Trim leading/trailing whitespace), "## Validation Rules" (alphanumeric plus underscore/hyphen, min/max length, case-insensitive, no leading/trailing hyphens, no consecutive underscores), "## Unicode Support", "## Error Handling" (Never throw exceptions, Return None for invalid input).
- **Status:** GOOD -- the prompt content is realistic and detailed. All four sections (Input Handling, Validation Rules, Unicode Support, Error Handling) match the kind of exhaustive specification needed "with few tests." The "51 lines" displayed actually says 50 lines on the header badge -- consistent with script.

### t=38s -- V5: ShortPromptTests
- **Script:** "A short, minimal prompt appears. Just a few requirements. But it's surrounded by dozens of test walls. File: `parser_v2.prompt` - 10 lines. Terminal shows: `pdd test parser` with 47 tests passing."
- **Actual:** `parser_v2.prompt` card with "10 lines" badge. Content: "# User ID Parser / Parse and validate user IDs from input. / Return None for any invalid input. / Handle all edge cases gracefully. / Never throw exceptions. / See tests for exact behavior."
- **Issue (MINOR):** Script calls for "surrounded by dozens of test walls" and terminal showing `pdd test parser` with 47 tests passing. At this frame, only the prompt card is visible without surrounding test indicators or terminal. The test walls appear later in the GraphAnimateCurve composition (V6).
- **Status:** GOOD -- the prompt itself is perfect. The contrast with V4's 50-line version is immediately clear.

### t=47s -- V6: GraphAnimateCurve
- **Script:** "Animate along the curve. At the left (few tests), the prompt must be very detailed. At the right (many tests), the prompt can be minimal."
- **Actual:** "The Precision Tradeoff" title. Inverse curve drawn on the graph. LEFT side: large `parser.prompt` document icon with many lines (positioned at "FEW TESTS" / high precision). RIGHT side: small amber test blocks (positioned at "MANY TESTS" / low precision). "FEW TESTS" and "MANY TESTS" labels below. X-axis: "Number of Tests".
- **Status:** EXCELLENT -- this is the visual payoff of Part 4. The inverse curve with prompt icon (left/large) and test blocks (right/small) instantly communicates the tradeoff. The spatial mapping (few tests = big prompt, many tests = small prompt) is intuitive.

### t=55s -- V7: BothGenerateFinal
- **Script:** "Both produce correct output. But one required a 50-line prompt, the other a 10-line prompt. Text: 'More tests, less prompt. The walls do the precision work.'"
- **Actual:** Side-by-side comparison: "VERSION 1" (left) with `parser_v1.prompt` (50 lines, dense with "...(40 more lines)" note) and `output.py` below. "VERSION 2" (right) with `parser_v2.prompt` (10 lines, compact) plus 47 amber test blocks and `output.py` below.
- **Status:** GOOD -- both versions generate the same `output.py`, making the point that identical output comes from different specification strategies. The "47 tests" grid of amber blocks next to the short prompt visually reinforces "the tests handle the constraints."
- **Issue (MINOR):** Script calls for "More tests, less prompt. The walls do the precision work." closing text. This text is not visible at t=55s. May appear in the final 3 seconds (t=56-59s) of the segment.

---

## Issues Summary

| Severity | Count | Description |
|----------|-------|-------------|
| MINOR | 1 | V5: Missing "pdd test parser" terminal and surrounding test walls (test grid appears in V6-V7 instead) |
| MINOR | 1 | V7: "More tests, less prompt" closing text not visible at t=55s |

---

## Overall Assessment

Part 4 is the most focused section -- 8 segments across 61s = ~7.6s average. The single-concept structure (precision tradeoff between prompt detail and test coverage) benefits from this conciseness. Key highlights:

1. **GraphAnimateCurve (V6):** The visual centerpiece. The inverse curve with prompt icon and test blocks on a labeled graph is immediately legible and memorable. Rated EXCELLENT.

2. **MoldFlowFocus (V2):** Outstanding Veo clip of transparent mold cross-section with liquid plastic. One of the best shots in the entire production -- the see-through mold makes the "walls constrain the flow" concept visceral.

3. **LongPrompt vs ShortPromptTests (V4-V5):** The `parser_v1.prompt` (50 lines, 4 sections) vs `parser_v2.prompt` (10 lines, "See tests for exact behavior") contrast is crisp and realistic. The prompt content is technically credible.

4. **BothGenerateFinal (V7):** Effective closing. Both versions producing `output.py` makes the equivalence point concrete.

5. **Pacing:** Tight and efficient. No segment overstays. The Veo clips (V0-V2, ~20s) set up the metaphor, the prompts (V4-V5, ~15s) show concrete examples, and the graph/comparison (V6-V7, ~15s) deliver the abstract takeaway.

**Blocking issues:** None
**Recommended improvements (non-blocking):**
1. V5: Add test wall indicators around parser_v2.prompt or terminal showing `pdd test parser` (LOW priority -- V7 handles this)
2. V7: Ensure "More tests, less prompt" closing text is visible (LOW priority)
