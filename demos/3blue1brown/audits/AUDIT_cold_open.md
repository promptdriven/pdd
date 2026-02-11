# S00 Cold Open Audit: The Sock Hook

**Video:** `outputs/sections/cold_open.mp4` (54s, 18.3 MB, 1920x1080, 30fps)
**Specs:** `specs/00-cold-open/` (01a through 01h)
**Script reference:** Lines 9-39 of main_script.md (COLD OPEN: THE SOCK HOOK, 0:00 - 2:00)
**Composition:** `remotion/src/remotion/S00-ColdOpen/ColdOpenSection.tsx`
**Date:** 2026-02-09

---

## Summary

| Severity | Count | Description |
|----------|-------|-------------|
| CRITICAL | 0 | -- |
| MAJOR    | 1 | V4 title card shows different code than V3B regenerated code (visual discontinuity) |
| MODERATE | 2 | V1B Remotion hold is stylistically jarring vs Veo clips; V0/V1 character inconsistency across Veo clips |
| MINOR    | 2 | V1/V1B gap flash at ~7.7s; V14 hold extends 0.22s past V1B start (brief overlap region) |

---

## Visual Segment Map

| Visual | Component | Time Range | Duration | Notes |
|--------|-----------|------------|----------|-------|
| V0 | Veo: cold_open_01a_establish | 0.0-4.92s | 4.92s | Split screen: developer + grandmother |
| V1 | Veo: cold_open_01d_zoom_out | 5.24-7.72s | 2.48s | Zoomed-out reveal |
| V1B | Remotion: HoldAccumulatedWeight | 7.72-13.72s | 6.0s | Contemplative split-screen hold |
| V2 | Veo: cold_open_01f_modern_sock_toss | 14.26-18.5s | 4.24s | Modern person tosses sock |
| V3 | Remotion: CodeBlinks | 18.78-28.78s | 10.0s | Patched code with blinking cursor |
| V3B | Remotion: CodeRegeneratesVisual | 28.78-43.78s | 15.0s | Delete, empty beat, regeneration, title crossfade |
| V4 | Remotion: TitleCardVisual | 43.78-53.78s | 10.0s | "Prompt-Driven Development" title card |

---

## Frame-by-Frame Analysis

### t=0s -- V0: Veo Establish Split Screen
- **Script says:** "Split screen. LEFT: Developer at keyboard, Cursor interface visible. RIGHT: 1950s great-grandmother carefully darning a wool sock by lamplight."
- **Actual:** Split screen with clean vertical divider. LEFT: Developer in blue sweater, glasses, typing on mechanical keyboard, cool blue monitor glow. RIGHT: Elderly grandmother with glasses, holding darning egg with sock, needle in hand, warm amber lamplight.
- **Status:** GOOD -- matches spec closely. Color temperature contrast (cool blue vs warm amber) is excellent. Both subjects framed identically at medium shot.

### t=1s-4s -- V0: Veo Establish Split Screen (continued)
- **Actual:** Smooth clip with subtle motion -- developer typing, grandmother working needle through sock. Both remain in frame and focused on their tasks.
- **Status:** GOOD -- natural movement, continuity maintained throughout 4.92s clip.
- **Note:** Developer's monitor does not visibly show a Cursor interface or code editor (script specifies "Cursor interface visible"). The monitor is mostly off-screen with just a glow. This is a minor departure from the literal script but is acceptable since the developer-at-keyboard visual communicates the concept.

### t=5s -- V0/V1 Transition
- **Actual:** Still showing the establish clip (V0 ends at 4.92s, V1 starts at 5.24s). The 0.32s gap is filled by the V0 clip continuing to play (loop is enabled on all Veo clips).
- **Status:** OK -- gap is imperceptible.

### t=6s -- V1: Veo Zoom Out
- **Script says:** "Zoom out on LEFT: single edit revealed as one of thousands of patches. Zoom out on RIGHT: Grandmother's drawer opens -- dozens of carefully mended items."
- **Actual:** New Veo clip. Split screen with different subjects -- LEFT: developer at multi-monitor setup with code windows visible, red indicator light. RIGHT: Grandmother in chair holding/knitting sock, oil lamp visible on table. Wider framing than V0.
- **Issue (MODERATE -- Character Inconsistency):** The developer in V1 is a DIFFERENT person than V0. V0 shows a younger man in blue sweater with lighter skin; V1 shows a different developer with darker complexion and different outfit. The grandmother also changes appearance -- V0 has her in an orange cardigan; V1 has her in a beige/cream cardigan. Since these are different Veo generations, character consistency was not maintained. The 0.32s gap and jump cut help somewhat, but attentive viewers will notice the character swap.

### t=7s -- V1: Veo Zoom Out (continued)
- **Actual:** Camera pulling back further, more code windows visible on left, grandmother's workspace expanding on right. Oil lamp creates warm glow.
- **Status:** OK -- zoom-out motion visible but subtle. The spec calls for a 14-second dolly zoom but V1 is only 2.48s long; the zoom-out is truncated.

### t=8s -- V1B: Remotion Hold on Accumulated Weight
- **Script says:** "Split screen holds. Both sides show the accumulated weight of all that careful repair work."
- **Actual:** HARD CUT from photorealistic Veo footage to Remotion-rendered illustration. LEFT: Dark blue background with file tree (src/components/, utils/, api/, etc.), floating TODO/FIXME/workaround comments in red, dependency graph nodes/edges, small IDE mockup with code, browser tabs, developer silhouette at bottom. RIGHT: Warm brown background with scattered sock/shirt/trouser icons, wooden table with darning egg, oil lamp SVG with animated flame, wicker basket, grandmother silhouette at bottom. White center divider.
- **Issue (MODERATE -- Style Jarring):** The transition from photorealistic Veo footage (t=7s) to flat Remotion illustration (t=8s) is visually jarring. The script implies a continuous hold on the zoomed-out composition. Instead, the viewer sees a completely different art style. The Remotion version does communicate the concept (accumulated weight on both sides, file tree + TODO comments on left, scattered mended items on right) but the stylistic break is noticeable. The white center divider matches the spec.
- **Mitigating factors:** (1) The spec for 01e says "must match exactly where zoom-out ended" which is impossible across Veo-to-Remotion transition. (2) The Remotion component has good detail: animated warning icons, cursor blinking, new TODO fading in, lamp flame flickering, grandmother breathing animation. These ambient details are well-implemented per spec.

### t=10s -- V1B: Remotion Hold (continued)
- **Actual:** Same composition. The "// TODO: fix race condition" label has faded in (visible at 12s too). Warning icon cycling position. Subtle ambient animations active.
- **Status:** OK -- contemplative hold working as intended despite style difference.

### t=12s -- V1B: Remotion Hold (continued)
- **Actual:** Same composition with "// TODO: fix race condition" fully visible. Ambient animations continue.
- **Status:** OK.

### t=14s -- V1B End / V2 Gap
- **Actual:** Still showing V1B (ends at 13.72s, V2 starts at 14.26s). The 0.54s gap shows the Remotion hold continuing.
- **Status:** OK.

### t=15s -- V2: Veo Modern Sock Toss
- **Script says:** "Hard cut to modern day. A person notices a hole in their sock. They shrug, toss it in the trash, and grab a fresh pair from a multi-pack."
- **Actual:** Young man in gray hoodie sitting on modern couch, looking down at his foot/sock. Modern apartment with plants, floor lamp, yellow pillows.
- **Status:** GOOD -- modern setting, casual relaxed vibe, clean hard cut from the weighted hold.

### t=16s -- V2: Veo Modern Sock Toss (continued)
- **Actual:** Close-up of hands examining white sock with visible hole in toe area.
- **Status:** GOOD -- the hole is clearly visible. Matches script's "notices a hole in their sock."

### t=18s -- V2: Veo Modern Sock Toss (continued)
- **Actual:** Person leaning forward toward what appears to be a small trash can, sock in hand.
- **Status:** GOOD -- the "toss in the trash" moment. Fresh pair on coffee table visible (folded clothes).
- **Note:** The script mentions "grab a fresh pair from a multi-pack" -- the fresh pair grab is not explicitly visible in the extracted frames, but the clip may show this in the intervening frames before V3 starts at 18.78s.

### t=19s -- V3: CodeBlinks (Patched Code)
- **Script says:** "Return to the code side. The cursor blinks on a complex function full of patches. Hold for a beat."
- **Actual:** Full-frame dark code editor. Filename tab "user_parser.py". Line numbers 47-79. The `parse_user_input` function with 33 lines of patched code visible: hotfix comments, unicode workarounds, "don't remove -- breaks downstream", legacy try/except, TODO comment, nested conditionals. Warning triangle on line 67 (TODO line). Blinking cursor visible on line 68. Git blame gutter with colored bands.
- **Status:** EXCELLENT -- this is a strong implementation. The code matches the spec exactly: patch-era color coding (lines 49-51 in warmer tint from hotfix, lines 54-56 in different tint for unicode fix, lines 60-72 warmest for refactor-todo era). Comment colors, keyword highlighting, and the "geological strata" effect all work. The cursor blink is the only motion, creating the contemplative beat the spec demands.

### t=20s-28s -- V3: CodeBlinks Hold
- **Actual:** Static hold on the patched code. Cursor blinks every ~0.53s. No other animation. Warning icon persistent. Subtle vignette increasing at edges near the end of the segment.
- **Status:** GOOD -- the "breathing room" shot is working. The code is readable and the accumulated patches are visually heavy. The narration "Code just got that cheap" lands during this hold, creating the intended ironic contrast.

### t=30s -- V3B: CodeRegenerates (Empty Beat)
- **Script says:** "The entire function DELETES. Then regenerates, clean, in under a second."
- **Actual:** Empty editor. Dark background (#1E1E2E). Filename tab "user_parser.py" still visible. Single blinking cursor at top-left (line 47, column 1). Terminal snippet in bottom-right corner showing `$ pdd generate user_parser`. No code visible.
- **Status:** EXCELLENT -- this is the "empty beat" that the spec calls "critical -- do not rush it." The deletion (selection flash + sweep) happened in frames 28.78-29.78s. At t=30s we see the result: a blank editor with just the cursor and terminal. The emptiness communicates "code is disposable." The terminal showing the command seeds the PDD concept subtly.

### t=32s -- V3B: CodeRegenerates (Post-Regeneration Hold)
- **Actual:** Clean regenerated code visible. 17 lines (47-63): `def parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:` with proper docstring (Args, Returns), type hints, clean logic. Terminal shows "$ pdd generate user_parser / Generating from prompt... / Done. (0.8s) checkmark" in green. Cursor blinking at end of function.
- **Status:** EXCELLENT -- the contrast is immediately visible: 17 clean lines vs 33 patched lines. No patch-era colors, no blame gutter bands, no warning icons. Standard syntax highlighting with uniform neutral gray. The terminal completion message is subtle but present. The line count reduction (33 -> 17, roughly half) is visually obvious without annotation, exactly as spec says.

### t=34s-40s -- V3B: Post-Regeneration Hold
- **Actual:** Static hold on clean code. Cursor blinks. Terminal persists.
- **Status:** GOOD -- the narration "So why are we still patching?" lands during this hold. The viewer is processing the visual contrast while the question resonates.

### t=42s -- V3B/V4 Overlap: Title Crossfade Begins
- **Actual:** "Prompt-Driven Development" title text beginning to appear overlaid on the regenerated code (which is starting to dim). The V3B component's TITLE_FADE_START at frame 360 (12s in) triggers the crossfade. The code behind is the full 17-line type-hinted version from the regeneration. Editor chrome still visible. Terminal still visible.
- **Status:** OK -- this is the crossfade from CodeRegeneratesVisual. The title is correctly beginning to emerge.

### t=44s -- V4: TitleCardVisual
- **Script says:** "Title card fades in over the regenerated code."
- **Actual:** V4 has taken over. The background shows a DIFFERENT, shorter code block inside a bordered box: `def parse_user_input(raw_input, context=None):` followed by simpler logic (`cleaned = raw_input.strip()`, `validate_and_normalize`). Editor chrome (dimming top bar with traffic light dots, line number gutter 47-54) still visible but fading. Terminal in bottom-right corner fading. Vignette beginning to appear.
- **Issue (MAJOR -- Code Discontinuity):** The code shown in V4's `TitleCardVisual` is a DIFFERENT function than V3B's regenerated code. V3B showed 17 lines with type hints (`str | None`, `dict | None`, docstring with Args/Returns). V4 shows ~7 lines without type hints, with a different implementation (`cleaned = raw_input.strip()`, `validate_and_normalize`). This is because `TitleCardVisual` has its own hardcoded code block in `ColdOpenSection.tsx:220` that doesn't match `CodeRegeneratesVisual`'s `NEW_CODE_LINES`. The viewer sees the code change between V3B and V4, breaking the illusion that the title is fading over the same regenerated code.
- **Fix suggestion:** Update the hardcoded code in `TitleCardVisual` (line ~220 of ColdOpenSection.tsx) to match the regenerated code from `CodeRegeneratesVisual.tsx`'s `NEW_CODE_LINES`. Both should show the same `parse_user_input` function with type hints and docstring.

### t=46s -- V4: TitleCardVisual (Title Settling)
- **Actual:** "Prompt-Driven Development" title fully visible, centered, white/warm-white text (#F8F4F0). Code behind is very dim (~0.15 opacity). Vignette active. Subtle blue glow behind title text visible. Editor chrome and terminal have faded out completely. The dimmed shorter code block is still faintly visible behind the title.
- **Status:** GOOD (aside from the code mismatch noted above). Title typography matches spec: ~72px, semi-bold, centered, clean sans-serif. The blue glow is subtle and atmospheric. Vignette creates natural focus on the title.

### t=48s-52s -- V4: Title Hold
- **Actual:** Pure stillness. Title centered with dimmed code texture behind. No animation. Vignette and glow at their final values.
- **Status:** GOOD -- the "poster frame" of the video. Works as a standalone still image. The silence (no narration during this segment) gives the title weight, as spec intends.

### t=53s -- V4: Final Frame
- **Actual:** Same composition, title at full opacity. Ready for transition to Part 1.
- **Status:** GOOD -- title remains at full opacity at the cut point, per spec.

---

## Systemic Issues

### 1. V4 TitleCardVisual Code Mismatch (MAJOR)
**Affects:** V4 (43.78-53.78s) -- 10 seconds

**Problem:** The `TitleCardVisual` component in `ColdOpenSection.tsx` (line ~220) contains a hardcoded code snippet that does not match the regenerated code from `CodeRegeneratesVisual.tsx`. The V3B regenerated code has 17 lines with type hints, docstring with Args/Returns, and clean type annotations. The V4 title card code has ~7 lines without type hints and a different implementation.

**Impact:** During the V3B-to-V4 transition (t=42s-44s), the background code visibly changes. This breaks the illusion of a continuous scene (title fading over regenerated code).

**Fix:** Replace the hardcoded pre-style code block in `TitleCardVisual` (ColdOpenSection.tsx:220) with the same code from `NEW_CODE_LINES` in CodeRegeneratesVisual.tsx:
```python
def parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:
    """Parse and validate user input string.

    Args:
        raw_input: The raw input string to parse, or None.
        context: Optional context dictionary for strict mode filtering.

    Returns:
        Parsed result dictionary, or error dictionary on failure.
    """
    if raw_input is None:
        return {"error": "null_input", "value": None}
    text = raw_input if isinstance(raw_input, str) else raw_input.decode("utf-8", errors="replace")
    result = _inner_parse(text)
    if context and context.get("strict_mode"):
        result = {k: v for k, v in result.items() if not k.startswith("_")}
    return result
```

### 2. Veo Character Inconsistency Between V0 and V1 (MODERATE)
**Affects:** V0-to-V1 transition (t=4.92s-5.24s)

**Problem:** The developer and grandmother are different people in V0 vs V1, due to separate Veo generations. V0: young man in blue sweater, grandmother in orange cardigan. V1: different developer, grandmother in beige cardigan.

**Impact:** Observant viewers will notice the character swap at the cut. The 0.32s gap and narration help mask it.

**Fix (if re-generating):** Use the same character reference/seed across Veo generations. Alternatively, accept this as a Veo limitation -- the jump cut style partially justifies it.

### 3. Veo-to-Remotion Style Break at V1B (MODERATE)
**Affects:** V1-to-V1B transition (t=7.72s)

**Problem:** Hard cut from photorealistic Veo footage to flat Remotion illustration. The accumulated-weight concept is well-communicated in both styles, but the art style transition is noticeable.

**Impact:** Viewer notices the switch from photorealistic to stylized. The Remotion version has good detail and ambient animations, so it works conceptually, but doesn't feel like a continuous camera hold.

**Fix (if desired):** Could be addressed by either (a) generating a longer Veo zoom-out clip that covers the full 6s hold, or (b) adding a brief crossfade transition between V1 and V1B to soften the cut. Alternatively, accept this as a deliberate style shift -- the Remotion version allows precise control over the visual elements (file tree, TODO labels, dependency graph) that Veo might not produce consistently.

---

## Strengths

1. **V3 CodeBlinks is outstanding** -- the patched function with layered patch-era colors, comment annotations, warning icon, blame gutter, and solitary blinking cursor creates exactly the "geological strata" feeling the spec describes.

2. **V3B empty beat is perfect** -- the blank editor with cursor and terminal command is the emotional fulcrum of the entire cold open. The silence is powerful.

3. **V3B regeneration contrast works** -- 33 patched lines reduced to 17 clean lines, with the terminal showing `Done. (0.8s)`, communicates the thesis instantly.

4. **V4 title card composition is strong** -- clean typography, subtle blue glow, dimmed code backdrop, vignette. Works as a poster frame.

5. **V2 sock toss is effective** -- the modern casual scene (couch, hoodie, visible hole, trash can) creates a clean break from the contemplative split-screen weight.

6. **V1B ambient animations are well-crafted** -- warning icon cycling, TODO fading in, lamp flame flickering, grandmother breathing. These add life to what could be a static hold.

---

## Status: PASS

**MAJOR issue resolved (2026-02-09 15:00):** The V4 TitleCardVisual code block in ColdOpenSection.tsx:220 was updated to match CodeRegeneratesVisual's NEW_CODE_LINES (17-line type-hinted function with docstring). Container width widened from 700 to 880px. Cold open re-rendered and visually verified at t=44s -- V4 now shows identical code to V3B.

**Non-blocking issues accepted:** The MODERATE style/character inconsistencies (Veo character swap at V0/V1, Veo-to-Remotion style break at V1/V1B) are inherent to the Veo+Remotion pipeline and accepted for this production pass.
