# Scene Audit: S01 V19 - ContextWindowComparison

**Section:** S01 Part 1 Economics
**Scene:** V19 - ContextWindowComparison (efficiency variant)
**Time range:** 320.92s - 365.0s (44.08s duration)
**Frames extracted:** t=325s, t=340s, t=355s, t=364s
**Remotion component:** `remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx`

---

## Verdict: PASS

---

## Script Requirements vs. Rendered Output

### Script visual description:
> "Side-by-side comparison. LEFT: 'Agentic patching' -- context window filled with 15,000 tokens of code, red highlights on irrelevant sections, tiny green section with relevant code. RIGHT: 'PDD regeneration' -- context window with a 300-token prompt, 2,000 tokens of tests, small grounding example. Clean. Focused. Room to think."

### Script narration:
> "And there's something else. These models are trained on up to thirty times more natural language than code. Natural language is their deepest fluency... A prompt is natural language. You're speaking the model's strongest language and giving it room to think."

---

## Frame-by-Frame Analysis

### Frame 1 (t=325s) -- Early build
- Side-by-side layout is established with a vertical divider.
- **LEFT panel:** Labeled "Agentic Patching" at top. Code window with macOS chrome dots (red/yellow/green). Code is filling in with Python-like patterns. Red-tinted background visible on irrelevant code zones. Small green-highlighted section visible in the middle of the code. One "IRRELEVANT" watermark starting to appear.
- **RIGHT panel:** Labeled "PDD Regeneration" at top. Chrome dots present. Blue "Prompt (300 tokens)" block visible. Amber "Tests (2,000 tokens)" block visible. Green "Grounding Example" block partially fading in. Large empty space below -- "Room to think" text not yet visible.
- Token counters not yet shown at this point.

### Frame 2 (t=340s) -- Full state
- **LEFT panel:** Fully populated with code. Two "IRRELEVANT" watermarks visible (rotated, semi-transparent). Red-tinted background on upper and lower sections. Small green-highlighted relevant section in the middle. Red glow visible on border. Token counter reads "15,000 tokens" in red below the window.
- **RIGHT panel:** All three blocks fully visible: blue "Prompt (300 tokens)", amber "Tests (2,000 tokens)", green "Grounding Example". "Room to think" text appears in gray italic in the empty space. Token counter reads "2,300 tokens" in blue below the window.
- **Center badge:** "6.5x fewer tokens" badge visible between the two panels in a rounded pill shape with blue border.
- **Bottom center:** "10x more system knowledge" text in green visible below the badge.

### Frame 3 (t=355s) -- Hold phase
- Identical to t=340s in content. All elements fully visible and in their final state.
- Subtle idle animation (pulse/shimmer) gives the scene a living quality.
- All labels, counters, badge, and knowledge indicator remain stable and readable.

### Frame 4 (t=364s) -- Late hold phase
- Identical composition to t=340s and t=355s. Scene is in its hold/breathe phase.
- All elements remain stable. No degradation, flicker, or unexpected changes.

---

## Checklist

| Criterion | Status | Notes |
|-----------|--------|-------|
| Side-by-side layout | PASS | Clear left/right panels with vertical divider |
| Left label "Agentic Patching" | PASS | Visible at top of left panel, white text, bold |
| Right label "PDD Regeneration" | PASS | Visible at top of right panel, white text, bold |
| Left: Code filling context window | PASS | ~85 lines of Python-like code fill the window |
| Left: Red highlights on irrelevant sections | PASS | Red-tinted background on upper ~42% and lower ~52% |
| Left: Green section for relevant code | PASS | Small green band visible at ~42-48% of the code |
| Left: "IRRELEVANT" watermarks | PASS | Two rotated watermarks appear over red zones |
| Left: 15,000 tokens counter | PASS | Red "15,000 tokens" shown below window |
| Right: Prompt (300 tokens) block | PASS | Blue block with label, proportionally small |
| Right: Tests (2,000 tokens) block | PASS | Amber block with label, proportionally larger |
| Right: Grounding Example block | PASS | Green block with label, small |
| Right: "Room to think" text | PASS | Gray italic text in the large empty space |
| Right: 2,300 tokens counter | PASS | Blue "2,300 tokens" shown below window |
| "6.5x fewer tokens" badge | PASS | Centered pill badge between panels |
| "10x more system knowledge" text | PASS | Green text below badge |
| Clean/focused right panel | PASS | Three tidy blocks with ample whitespace |
| Cluttered left panel | PASS | Dense code with red/green zones conveys clutter |
| Color contrast and readability | PASS | All text legible against dark background |
| Animation timing | PASS | Progressive reveal; hold phase stable |
| Variant correctly set | PASS | `variant="efficiency"` used in composition |

---

## Component Code Review

The component at `remotion/src/remotion/14a-ContextWindowComparison/ContextWindowComparison.tsx` (802 lines) supports two variants (`efficiency` and `density`). For S01 V19, the `efficiency` variant is correctly used, as confirmed in the composition file at `Part1Economics.tsx` line 199.

Key constants from `constants.ts`:
- `TOKEN_COUNTS.left = 15000`, `TOKEN_COUNTS.right = 2300` -- correct
- `RIGHT_BLOCKS`: promptHeight 15%, testsHeight 25%, groundingHeight 10%, emptyHeight 50% -- proportions communicate the "room to think" concept effectively
- Code patterns: 85 lines of realistic Python code (auth, database, events, rate limiting)
- Beat timings well-structured across 15 seconds (450 frames at 30fps)
- Badge text hardcoded as "6.5x fewer tokens" (15000/2300 = 6.52x, mathematically accurate)

---

## Summary

The scene is a faithful and visually effective implementation of the script description. The side-by-side comparison clearly contrasts the cluttered, code-heavy "Agentic Patching" context window (15,000 tokens with red irrelevant highlights and a tiny green relevant zone) against the clean, focused "PDD Regeneration" window (300-token prompt, 2,000-token tests, grounding example, and ample "room to think"). The "6.5x fewer tokens" badge and "10x more system knowledge" indicator reinforce the message. All elements match the script's intent. The animation builds progressively and holds stable for the narration. No issues found.
