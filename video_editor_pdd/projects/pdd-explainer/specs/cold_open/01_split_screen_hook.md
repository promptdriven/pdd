[split:]

# Section 0.1: Split Screen Hook — Developer Meets Grandmother

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:00 - 0:08

## Visual Description

The video opens cold on a vertical split screen. LEFT panel: a modern developer's hands on a keyboard, Cursor IDE visible on a monitor — syntax-highlighted code, an inline AI suggestion ghosting in, the developer accepting it with a keystroke. The edit lands cleanly, a green diff marker appears. RIGHT panel: a 1950s great-grandmother sitting under warm lamplight, carefully pulling thread through a wool sock stretched over a wooden darning egg. Her stitches are precise, methodical, practiced. Both complete their respective repair tasks simultaneously — the parallel is unmistakable but unstated. A thin vertical divider separates the two worlds.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (dark IDE)
- Split divider: vertical line at x: 960, `#334155` at 0.4, 2px solid

### Chart/Visual Elements

**LEFT Panel (x: 0-958)**
- Veo clip: `developer_cursor_edit` (see companion spec `05_developer_cursor_broll.md`)
- Color grading overlay: `#4A90D9` at 0.02 (cool blue tint)
- Vignette: radial gradient from transparent center to `#000000` at 0.15 edges
- Panel header: "2025" — Inter SemiBold 16px, `#8B949E` at 0.6, top-left at (24, 20)

**RIGHT Panel (x: 962-1920)**
- Veo clip: `grandmother_darning` (see companion spec `02_grandmother_lamplight.md`)
- Color grading overlay: `#D4A043` at 0.04 (warm amber tint)
- Vignette: radial gradient from transparent center to `#0A0500` at 0.2 edges
- Film grain overlay: monochrome noise, 0.06 opacity, animated at 12fps
- Panel header: "1955" — Inter SemiBold 16px, `#8B949E` at 0.6, top-left at (986, 20)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade in from black. Both panels appear simultaneously — the split is revealed instantly, no wipe. Opacity 0 → 1 over 15 frames.
2. **Frame 15-120 (0.5-4s):** Both clips play in parallel. LEFT: developer's hands type, AI suggestion ghosts in, cursor accepts with Tab. RIGHT: grandmother pulls thread through fabric, turns the sock, makes another stitch.
3. **Frame 120-180 (4-6s):** Both tasks complete. LEFT: green diff marker slides in from the left gutter. RIGHT: grandmother ties off the thread, holds the sock up to inspect.
4. **Frame 180-240 (6-8s):** Hold on the completed work. Both sides satisfied. A subtle shared glow pulses on the divider line — `#4A90D9` to `#D9944A` gradient, 0.3 opacity, 1s cycle.

### Typography
- Panel headers: Inter SemiBold, 16px, `#8B949E` at 0.6
- No other text — visuals carry the moment

### Easing
- Fade in: `easeOut(cubic)` — fast reveal, gentle settle
- Divider glow: `sine` oscillation — smooth pulse

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_001` | "If you use Cursor, or Claude Code, or Copilot..." | Frame 15 — narration begins as panels become visible |
| `cold_open_002` | "...you're getting really good at this." | Frame 140 — lands as both tasks complete |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Fade-in wrapper */}
  <Sequence from={0} durationInFrames={15}>
    <FadeIn>
      <SplitScreen dividerX={960} dividerColor="#334155" dividerOpacity={0.4}>
        <LeftPanel>
          <VeoClip clipId="developer_cursor_edit" />
          <ColorGrade tint="#4A90D9" opacity={0.02} />
          <Vignette color="#000000" opacity={0.15} />
          <PanelHeader text="2025" x={24} y={20} />
        </LeftPanel>
        <RightPanel>
          <VeoClip clipId="grandmother_darning" />
          <ColorGrade tint="#D4A043" opacity={0.04} />
          <FilmGrain opacity={0.06} fps={12} />
          <PanelHeader text="1955" x={986} y={20} />
        </RightPanel>
      </SplitScreen>
    </FadeIn>
  </Sequence>

  {/* Divider glow pulse at completion */}
  <Sequence from={180} durationInFrames={60}>
    <DividerGlow
      x={960}
      gradientColors={["#4A90D9", "#D9944A"]}
      opacity={0.3}
      cycleDuration={30}
    />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical",
  "divider": { "x": 960, "color": "#334155", "opacity": 0.4, "width": 2 },
  "panels": {
    "left": {
      "label": "2025",
      "veoClipId": "developer_cursor_edit",
      "colorGrade": { "tint": "#4A90D9", "opacity": 0.02 },
      "vignette": { "color": "#000000", "opacity": 0.15 }
    },
    "right": {
      "label": "1955",
      "veoClipId": "grandmother_darning",
      "colorGrade": { "tint": "#D4A043", "opacity": 0.04 },
      "filmGrain": { "opacity": 0.06, "fps": 12 }
    }
  },
  "embeddedVeoClips": ["developer_cursor_edit", "grandmother_darning"],
  "narrationSegments": ["cold_open_001", "cold_open_002"]
}
```

<!-- ANNOTATION_UPDATE_START: 0d83f57f-c624-4283-a3c4-54a88b83d493 -->
## Annotation Update
Requested change: The frame is sampled at frame 104/120 (87.5% through the animation), which falls in the hold phase (frames 90-120). Most elements are correctly present and positioned:

**Passing elements:**
- Background: Deep navy-black background is correct.
- "PART 3": Visible above the title text with letter-spacing, correct muted color, correctly positioned.
- "THE MOLD HAS": Large bold white text, correctly rendered and centered.
- "THREE PARTS": Large bold white text, rendered below the first line.
- Ghost shapes: At least two ghost shapes are faintly visible — a rectangular block structure on the left (wall segment) and a circular/nozzle shape on the right. A center shape (funnel/nozzle) is very faintly visible behind the text. The shapes are at very low opacity as specified.

**Minor issues:**
- **Horizontal rule missing:** The spec calls for a 200px wide, 2px horizontal rule at `#334155` (0.5 opacity) centered between the two title lines at approximately y:505. No horizontal rule is visible in the rendered frame. This should have been fully drawn by frame 70 and held through the end.
- **Ghost labels missing:** The spec calls for tiny labels ("WALLS", "NOZZLE", "MATERIAL") beneath each ghost shape at 0.03 opacity. These are not visible. However, at 0.03 opacity and 8px font size, these would be nearly imperceptible, so this is borderline.
- **Blueprint grid not clearly visible:** The spec calls for a subtle blueprint grid at 0.05 opacity. The background appears smooth without a visible grid pattern, though at such low opacity this may simply not be perceptible in the compressed frame.
- **"THREE PARTS" offset-right:** The spec calls for a 15px right offset on "THREE PARTS" relative to center. The text appears roughly centered rather than offset, though this is a subtle positioning detail.
Technical assessment: Frame 104/120 (hold phase). Primary elements — background, 'PART 3' label, 'THE MOLD HAS', 'THREE PARTS', and ghost shapes — are correctly rendered. However, the 200px horizontal rule specified at y:505 between the two title lines (#334155, 0.5 opacity, 2px height) is completely absent. This is a deliberate design element that should have been fully drawn by frame 70 and held through the end. The rule should be clearly visible at 0.5 opacity against the #0A0F1A background. Secondary issues: ghost labels at 0.03 opacity and blueprint grid at 0.05 opacity are not visible but are borderline-imperceptible by design. The 15px right offset on 'THREE PARTS' is not apparent but is a subtle positioning detail.
- Add or fix the DrawLine component rendering the horizontal rule: 200px wide, 2px height, color #334155 at 0.5 opacity, centered horizontally at y:505, drawing from center outward starting at frame 60 over 10 frames
- Verify 'THREE PARTS' text x-position is 975px (15px right of center 960px) per spec
- Optionally verify blueprint grid is rendering at 60px spacing with #1E293B at 0.05 opacity — may need slight opacity increase if grid is desired to be subtly visible after video compression
<!-- ANNOTATION_UPDATE_END: 0d83f57f-c624-4283-a3c4-54a88b83d493 -->

<!-- ANNOTATION_UPDATE_START: 356bd043-74bf-4580-bc81-1001982ae317 -->
## Annotation Update
Requested change: The frame is at 90.5% progress (frame 379/420), corresponding to the final hold phase where perfect parts should be visible with green checkmarks and the mold pulses with amber glow. Several critical and major issues are visible: (1) The background uses a photographic factory floor image instead of the specified #0A0F1A deep navy-black with faint 40px drafting grid — this is a fundamental departure from the clean vector/engineering-diagram aesthetic. (2) The ejected parts below the mold appear as plain gray rectangles without clearly visible green checkmark overlays, which are critical at this phase ('perfect parts continue appearing' with green checkmarks). (3) The mold shape and amber coloring are correctly rendered and centered. (4) Labels for 'Fix the mold' and 'All future parts: fixed' appear to be present in approximately correct positions. The photographic background significantly undermines the specified 'clean, technical' engineering-diagram aesthetic and makes the overlay elements harder to read.
Technical assessment: Frame 379/420 (final hold phase) shows two critical deviations from spec. (1) The background is a photographic factory floor image instead of the specified solid #0A0F1A deep navy-black with faint 40px drafting grid (#1E293B at 0.04 opacity). This is a Remotion composition issue — the AbsoluteFill backgroundColor should be #0A0F1A with a DraftGrid overlay, but instead a photographic/video background layer is being composited behind the diagram elements. (2) The ejected parts below the mold appear as plain gray rectangles (~#94A3B8) without the required green checkmark overlays (#5AAA6E). At frame 379, we are deep in the Act 3 hold phase (frames 340-420) where 'perfect parts continue appearing' with green checkmarks visible on each. The mold shape, amber wall coloring, center positioning, and label placement are approximately correct, but these are overshadowed by the two critical failures. The photographic background also degrades label readability, making the 'Fix the mold' (#D9944A) and 'All future parts: fixed' (#5AAA6E) text difficult to parse against the busy factory imagery.
- Replace the background layer in the Remotion composition with AbsoluteFill backgroundColor '#0A0F1A' and add a DraftGrid component with 40px spacing, color '#1E293B', opacity 0.04 — remove any photographic/video background source
- Add green checkmark overlays (#5AAA6E at 0.5) to each ejected part in the FixedPartsSequence component — checkmarks should pop in with easeOut(back(1.5)) scale animation as specified
- Verify the z-index layering so that the solid background is behind all diagram elements and the drafting grid renders at the correct low opacity
- Confirm labels 'Fix the mold' and 'All future parts: fixed' have correct typography (Inter 14px, semi-bold 600 for mold label) and opacity values once background is corrected
<!-- ANNOTATION_UPDATE_END: 356bd043-74bf-4580-bc81-1001982ae317 -->

<!-- ANNOTATION_UPDATE_START: 5985a916-5eba-4b56-992d-297b101b0ada -->
## Annotation Update
Requested change: The title card layout is correct: 'Prompt-Driven Development' is centered horizontally with bold typography, the subtitle 'WHY YOU'RE STILL DARNING SOCKS' appears below in uppercase with lighter weight, and a thin horizontal rule is visible between them. The vertical stacking order (title above line, subtitle below) and horizontal centering all match spec. However, the sampled frame is at 91.7% progress (frame 164/180), which falls squarely in the fade-out phase (frames 150-180). At this point, the entire composition should be fading out with decreasing opacity. Instead, the title card elements appear at near-full opacity — the title and subtitle are clearly legible with no visible fade-out occurring. Additionally, the background color appears as a medium gray (~#4B5263) rather than the specified deep navy (#0A0F1A). The background is far too bright and lacks the dark, rich navy tone specified. The background constellation dots are not visibly present. The horizontal rule has the correct gradient-to-transparent appearance and is properly positioned. The title text color reads as a light gray which is reasonable, and the subtitle is appropriately muted.
Technical assessment: Three issues identified, all in the Remotion composition layer. (1) Background color is ~#4B5263 (medium gray) instead of the specified #0A0F1A (deep navy). This is a clear color mismatch — the background is roughly 4x too bright and lacks any blue/navy tint. (2) Fade-out animation is not functioning: frame 164 falls at ~47% through the fade-out window (frames 150-180), so all elements should be at roughly 53% of their hold-phase opacity, yet title, subtitle, and rule all appear at near-full opacity with no visible dimming. The fade-out sequence is either not applied or not wrapping the child elements correctly. (3) Background constellation dots (50 circles, #4A90D9 at 0.06 opacity, 1-2px) are not visible — though at 0.06 opacity on a too-bright gray background they could be washed out entirely. Layout, typography, text content, horizontal rule position, and vertical stacking are all correct per spec.
- Set the AbsoluteFill backgroundColor to '#0A0F1A' — verify the value is not being overridden by a parent container or theme default
- Fix the fade-out sequence (frames 150-180): ensure the FadeOut wrapper actually encloses all child elements (title, subtitle, rule, dots) so their opacity decreases from full to 0 over 30 frames. The current Remotion code structure shows FadeOut as a sibling Sequence rather than wrapping the content — restructure so all visible elements inherit the fade
- Verify DriftingDots component is rendering and that dots are visible against the corrected #0A0F1A background at 0.06 opacity
<!-- ANNOTATION_UPDATE_END: 5985a916-5eba-4b56-992d-297b101b0ada -->
