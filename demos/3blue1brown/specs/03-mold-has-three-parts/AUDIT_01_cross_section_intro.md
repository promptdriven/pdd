# Audit: Cross-Section Introduction (01_cross_section_intro)

## Status: ISSUES FOUND

### Requirements Met

1. **Resolution:** Canvas is 1920x1080 as specified. SVG viewBox matches (`"0 0 1920 1080"`). (`constants.ts` lines 8-9)
2. **Background color:** Dark background `#1a1a2e` applied via AbsoluteFill. (`constants.ts` line 26, `CrossSectionIntro.tsx` line 100)
3. **Duration:** 15 seconds at 30fps (450 frames). (`constants.ts` lines 4-7)
4. **Beat timings match spec exactly:**
   - Frame 0-90: Mold outline fades in (`BEATS.OUTLINE_START=0, OUTLINE_END=90`)
   - Frame 90-150: Walls highlight (`BEATS.WALLS_START=90, WALLS_END=150`)
   - Frame 150-210: Nozzle highlights (`BEATS.NOZZLE_START=150, NOZZLE_END=210`)
   - Frame 210-270: Material highlights (`BEATS.MATERIAL_START=210, MATERIAL_END=270`)
   - Frame 270-450: All three visible (`BEATS.ALL_VISIBLE_END=450`)
   - (`constants.ts` lines 12-22)
5. **Region colors correct:** Walls amber `#D9944A`, Nozzle blue `#4A90D9`, Material green `#5AAA6E`. (`constants.ts` lines 27-29)
6. **Label names correct:** "Walls", "Nozzle", "Material" as single-line labels at 24px bold. (`CrossSectionIntro.tsx` lines 212, 230, 248)
7. **Labels fade in with their respective regions:** Each label opacity is driven from its region's start time, not delayed. (`CrossSectionIntro.tsx` lines 36-43, 63-70, 90-97)
8. **Pulse animation present:** Each region has a 40-frame pulse (0 -> 0.3 -> 0 amplitude) using `Easing.inOut(Easing.sin)`, matching spec's `easeInOutSine`. (`CrossSectionIntro.tsx` lines 27-34, 54-61, 81-88)
9. **Easing - mold fade-in:** `Easing.out(Easing.cubic)` matches spec's `easeOutCubic`. (`CrossSectionIntro.tsx` line 14)
10. **Easing - region highlights:** `Easing.out(Easing.quad)` matches spec's `easeOutQuad`. (`CrossSectionIntro.tsx` lines 23, 50, 77)
11. **Easing - label fade-in:** `Easing.out(Easing.cubic)` matches spec's `easeOutCubic`. (`CrossSectionIntro.tsx` lines 41, 68, 95)
12. **Glow effect on active regions:** CSS `drop-shadow` filter applied to each region when its glow value > 0, with intensity scaling by both glow and pulse. (`CrossSectionIntro.tsx` lines 128-129, 171, 189)
13. **Three distinct regions rendered:** Walls (left, right, bottom rects), Nozzle (top rect), Interior/Material (dashed interior rect). Layout matches the spec diagram. (`CrossSectionIntro.tsx` lines 116-192)
14. **Section integration:** CrossSectionIntro is wired as Visual 0 in `S03-MoldThreeParts/Part3MoldThreeParts.tsx` (lines 48-52), starting at frame 0 and running through ~12.26s of the section timeline.
15. **showLabels prop:** Supports toggling labels on/off, used in the section composition with default `true`. (`constants.ts` lines 47-55)

### Issues Found

1. **Outline gray color mismatch (Low)**
   - **Spec says:** Steel gray `#8A9BA8` base color for the mold
   - **Implementation does:** Uses `#5a6a7a` (OUTLINE_GRAY) which is noticeably darker
   - **Location:** `constants.ts` line 30
   - **Impact:** The mold outline appears darker and less "steel-like" than specified

2. **No grid lines for technical feel (Low)**
   - **Spec says:** "Subtle grid lines for technical feel" on the mold cross-section
   - **Implementation does:** Plain SVG rectangles with no grid overlay
   - **Location:** `CrossSectionIntro.tsx` lines 101-193 (entire SVG block)
   - **Impact:** Missing visual polish element; the rendering is clean but lacks the blueprint/technical aesthetic

3. **No 3D-ish perspective (Low)**
   - **Spec says:** "3D-ish perspective showing internal structure" and "Technical, blueprint-style rendering"
   - **Implementation does:** Flat 2D rectangles in SVG. No depth cues, no perspective transform, no blueprint styling
   - **Location:** `CrossSectionIntro.tsx` SVG rendering
   - **Impact:** The mold reads as a 2D schematic rather than a cross-section with depth

4. **Title text not in spec (Low - Addition)**
   - **Spec says:** No title text mentioned in the visual description
   - **Implementation does:** Adds "The Mold Has Three Parts" title at bottom center, fading in with the outline
   - **Location:** `CrossSectionIntro.tsx` lines 255-269
   - **Impact:** Non-contradictory addition; provides helpful context

5. **Audio cues not implemented (Low)**
   - **Spec says:** "Subtle mechanical/technical ambient" and "Soft ping on each region highlight"
   - **Implementation does:** No audio elements in the CrossSectionIntro component itself (audio is handled at the S03 section level with narration only)
   - **Location:** N/A
   - **Impact:** Missing sound design layer; narration audio is present at the section level but per-region pings are absent

### Notes

- All previously identified high-severity issues from the prior audit (label name mismatch, duration mismatch, timing sequence differences) have been fully resolved. The implementation now matches the spec on all critical dimensions.
- The remaining issues are all low-severity visual polish items (outline color shade, grid lines, 3D perspective, audio pings). None affect the core animation logic, timing, labeling, or color scheme.
- The component's internal 450-frame duration exceeds its allocation in the S03 section timeline (~368 frames / 12.26s at VISUAL_00_END). This means the "all three visible" hold phase (frames 270-450) may be cut short by the section transition to WallsIlluminate at ~13.44s. This is acceptable since the narration moves on and the next visual takes over.
- The `showLabels` prop provides flexibility for reuse in other contexts where labels might be suppressed.
