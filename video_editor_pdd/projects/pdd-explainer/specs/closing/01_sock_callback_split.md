[split:]

# Section 7.1: Sock Callback — The Final Discard

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 24:15 - 24:23

## Visual Description

The sock metaphor returns one final time as a vertical split screen. LEFT panel: a holey sock in close-up — someone considers it for a beat, then discards it and grabs a fresh one from a multi-pack. RIGHT panel: code with a bug highlighted — a developer considers it, then instead of opening the file to patch, they add a test and hit regenerate. Both actions happen simultaneously — discard and replace, not repair.

The left panel carries warm amber tones (matching the grandmother's world throughout the video). The right panel has cool blue-white monitor glow. Both halves embed Veo clips for live-action feel, with the split framing and text overlays controlled by Remotion.

Below the split, synchronized cost labels appear: "$2" under the sock (cost of new pair) and "~30s" under the code (regeneration time). The economics are now self-evident.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Panel Headers
- LEFT: "DISCARD" — Inter, 12px, semi-bold (600), `#D9944A` at 0.3, letter-spacing 3px, centered at y: 36
- RIGHT: "REGENERATE" — Inter, 12px, semi-bold (600), `#4A90D9` at 0.3, letter-spacing 3px, centered at y: 36

#### Left Panel — Sock Discard (x: 0 to x: 958)
- Background: warm amber grade over Veo clip
- Veo clip placeholder: hands holding a holey sock, considering, then tossing it aside and grabbing fresh pair from multi-pack
- Color grade overlay: `#D4A043` at 0.03, warm tone
- Subtle vignette: radial gradient, edges darkened to `#0A0500` at 0.25
- Cost label: "$2" — Inter, 28px, bold (700), `#D9944A` at 0.7, centered at y: 960
- Sub-label: "new pair" — Inter, 11px, `#94A3B8` at 0.4, centered at y: 990

#### Right Panel — Code Regeneration (x: 962 to x: 1920)
- Background: cool blue grade over Veo clip
- Veo clip placeholder: developer at monitor, code with bug visible, closes file, types `pdd bug → pdd fix` in terminal
- Color grade overlay: `#4A90D9` at 0.02, cool blue tone
- Subtle vignette: radial gradient, edges darkened to `#000510` at 0.25
- Cost label: "~30s" — Inter, 28px, bold (700), `#4A90D9` at 0.7, centered at y: 960
- Sub-label: "regenerated" — Inter, 11px, `#94A3B8` at 0.4, centered at y: 990
- Terminal snippet (bottom-right corner): `pdd bug → pdd fix → ✓` — JetBrains Mono, 10px, `#4A90D9` at 0.25, at (1780, 1020)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line draws from center outward. Panel headers "DISCARD" and "REGENERATE" fade in.
2. **Frame 15-60 (0.5-2s):** Both Veo clips begin. Left: hands hold holey sock, examining it. Right: developer looks at buggy code on screen.
3. **Frame 60-120 (2-4s):** Left: sock is tossed aside, hand reaches for fresh pack. Right: developer closes the file, opens terminal.
4. **Frame 120-160 (4-5.3s):** Left: fresh sock pulled from pack. Right: terminal shows `pdd bug → pdd fix → ✓`. Green checkmark appears.
5. **Frame 160-200 (5.3-6.7s):** Cost labels fade in simultaneously: "$2" (left), "~30s" (right). Sub-labels follow.
6. **Frame 200-240 (6.7-8s):** Hold on complete split. The parallel is self-evident.

### Typography
- Panel headers: Inter, 12px, semi-bold (600), respective colors at 0.3, letter-spacing 3px
- Cost labels: Inter, 28px, bold (700), respective colors at 0.7
- Sub-labels: Inter, 11px, `#94A3B8` at 0.4
- Terminal snippet: JetBrains Mono, 10px, `#4A90D9` at 0.25

### Easing
- Split line draw: `easeOut(cubic)` over 12 frames
- Panel header fade: `easeOut(quad)` over 12 frames
- Cost label fade: `easeOut(quad)` over 18 frames
- Sub-label fade: `easeOut(quad)` over 12 frames, 6-frame delay after cost label

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

Segment: `closing_001`

- **24:15** ("You don't patch socks"): Split appears, both Veo clips begin
- **24:17** ("because socks got cheap"): Left panel — sock tossed aside
- **24:19** ("The economics made patching"): Right panel — developer closes file, regenerates
- **24:21** ("irrational"): Cost labels appear — "$2" and "~30s"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Sock discard */}
    <Panel x={0} width={958}>
      <VeoClip clipId="sock_final_discard"
        src="/clips/sock_final_discard.mp4" fit="cover" />
      <ColorGrade color="#D4A043" opacity={0.03} />
      <Vignette edgeColor="#0A0500" edgeOpacity={0.25} />
      <PanelHeader text="DISCARD" color="#D9944A"
        opacity={0.3} letterSpacing={3} y={36} />
      <Sequence from={160}>
        <FadeIn duration={18}>
          <Text text="$2" font="Inter" size={28} weight={700}
            color="#D9944A" opacity={0.7} x={479} y={960} align="center" />
        </FadeIn>
        <Sequence from={6}>
          <FadeIn duration={12}>
            <Text text="new pair" font="Inter" size={11}
              color="#94A3B8" opacity={0.4} x={479} y={990} align="center" />
          </FadeIn>
        </Sequence>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.15} drawDuration={12} />

    {/* Right panel — Code regeneration */}
    <Panel x={962} width={958}>
      <VeoClip clipId="code_regenerate_callback"
        src="/clips/code_regenerate_callback.mp4" fit="cover" />
      <ColorGrade color="#4A90D9" opacity={0.02} />
      <Vignette edgeColor="#000510" edgeOpacity={0.25} />
      <PanelHeader text="REGENERATE" color="#4A90D9"
        opacity={0.3} letterSpacing={3} y={36} />
      <Sequence from={160}>
        <FadeIn duration={18}>
          <Text text="~30s" font="Inter" size={28} weight={700}
            color="#4A90D9" opacity={0.7} x={1441} y={960} align="center" />
        </FadeIn>
        <Sequence from={6}>
          <FadeIn duration={12}>
            <Text text="regenerated" font="Inter" size={11}
              color="#94A3B8" opacity={0.4} x={1441} y={990} align="center" />
          </FadeIn>
        </Sequence>
      </Sequence>
      <TerminalSnippet text="pdd bug → pdd fix → ✓"
        font="JetBrains Mono" size={10}
        color="#4A90D9" opacity={0.25} x={1780} y={1020} />
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "label": "DISCARD",
    "content": "sock_final_discard_veo",
    "colorGrade": { "color": "#D4A043", "opacity": 0.03 },
    "costLabel": "$2",
    "costSubLabel": "new pair",
    "background": "#000000"
  },
  "rightPanel": {
    "label": "REGENERATE",
    "content": "code_regenerate_callback_veo",
    "colorGrade": { "color": "#4A90D9", "opacity": 0.02 },
    "costLabel": "~30s",
    "costSubLabel": "regenerated",
    "terminalSnippet": "pdd bug → pdd fix → ✓",
    "background": "#000000"
  },
  "embeddedVeoClips": ["sock_final_discard", "code_regenerate_callback"],
  "backgroundColor": "#000000",
  "narrationSegments": ["closing_001"]
}
```

---

<!-- ANNOTATION_UPDATE_START: cc1a488b-a02f-4ea4-92f9-ed94f61f8b75 -->
## Annotation Update
Requested change: The frame is sampled at 91.7% progress (frame 219/240), which falls in animation phase 6 (frame 200-240: 'Hold on complete split'). At this point the spec requires the complete split view with cost labels, sub-labels, and panel headers all fully visible. Assessment of visible elements:

1. **Split layout**: PASS — Vertical split is present with left and right panels roughly divided at center. The divider line between panels is visible.
2. **Left panel content**: PASS — Shows hands holding a pack
Technical assessment: Frame 219/240 is in phase 6 (hold on complete split) where all text overlays should be at their final hold opacity and clearly legible. The split layout and Veo clip content are correct — left panel shows warm amber sock scene, right panel shows cool blue developer/keyboard scene. However, multiple required Remotion text overlays are missing or illegible: (1) 'DISCARD' panel header on the left is not visible at all (spec: Inter 12px, #D9944A at 0.3, y:36). (2) 'REGENERATE' panel header on the right is barely discernible. (3) '$2' cost label on the left is missing (spec: Inter 28px bold, #D9944A at 0.7, y:960). (4) '~30s' cost label on the right is barely visible (spec: Inter 28px bold, #4A90D9 at 0.7, y:960). (5) Sub-labels 'new pair' and 'regenerated' are not visible. (6) Terminal snippet 'pdd bug → pdd fix → ✓' is not visible. These are Remotion-layer text overlays that should have fully faded in by frame 178 (cost labels) and frame 172 (headers), so at frame 219 they should all be at full hold opacity. The underlying Veo footage is fine.
- Increase panel header opacity from 0.3 to at least 0.5-0.6 for both 'DISCARD' and 'REGENERATE' headers, or verify that the FadeIn sequence for headers is completing correctly
- Verify cost label positioning — '$2' at y:960 and '~30s' at y:960 may be rendering off-screen or behind the Veo clip layers; ensure text layers render above the VeoClip and ColorGrade layers in the z-order
- Ensure the FadeIn components for cost labels (from frame 160, duration 18) and sub-labels (from frame 166, duration 12) are not being clipped or masked by panel overflow:hidden styles
- Increase cost label opacity from 0.7 to 0.85-0.9 to ensure legibility against the Veo footage backgrounds, particularly the amber tones on the left
- Add a subtle dark gradient strip behind the text overlay regions (bottom 15% of each panel and top header bar) to improve contrast without obscuring the Veo footage
<!-- ANNOTATION_UPDATE_END: cc1a488b-a02f-4ea4-92f9-ed94f61f8b75 -->

<!-- ANNOTATION_UPDATE_START: 55bc4d1b-a9ad-4d5b-8943-f837ef506cc8 -->
## Annotation Update
Requested change: The split layout, Veo clip content, color grading, vertical divider, and cost labels ('$2' and '~30s') are all present and correctly positioned. However, at frame 219/240 (91.7% progress, within the 200-240 'hold on complete split' phase), three text overlay issues are noted: (1) The 'DISCARD' panel header at the top of the left panel is not clearly visible — it may be too faint or absent, while 'REGENERATE' on the right is faintly visible. (2) The sub-labels ('new pair' and 'regenerated') benea
Technical assessment: Frame 219/240 is in phase 6 (hold on complete split, frames 200-240) where all text overlays should be at their final hold opacity. The split layout, Veo clip content, color grading, and vertical divider are all correct. The primary cost labels ('$2' and '~30s') are present but several required Remotion text overlays are missing or illegible: (1) 'DISCARD' panel header at y:36 is not visible — spec calls for Inter 12px semi-bold at opacity 0.3 in #D9944A, but 0.3 opacity is too low against the warm amber Veo footage. (2) 'REGENERATE' panel header is only faintly discernible. (3) Sub-labels 'new pair' and 'regenerated' at y:990 in #94A3B8 at opacity 0.4 are not visible — likely obscured by Veo footage or z-order issues. (4) Terminal snippet 'pdd bug → pdd fix → ✓' at opacity 0.25 is invisible against the blue-lit scene. All FadeIn sequences should have completed by frame 178 at latest, so this is not a timing issue — it is an opacity and contrast problem with the text layers rendering over bright Veo footage.
- Increase 'DISCARD' and 'REGENERATE' panel header opacity from 0.3 to 0.55-0.6 and add a subtle dark gradient bar (rgba(0,0,0,0.4), ~50px tall) behind the header text region at y:20-60 to ensure legibility against the Veo footage
- Verify z-order stacking: ensure PanelHeader, cost label Text, and sub-label Text components render ABOVE VeoClip, ColorGrade, and Vignette layers in the JSX tree (later children = higher z-index in AbsoluteFill)
- Increase sub-label opacity from 0.4 to 0.55 for 'new pair' and 'regenerated', and verify y:990 positioning is not clipped by any panel overflow:hidden or bottom vignette masking
- Increase terminal snippet opacity from 0.25 to 0.4 and add a small dark backing patch behind it for contrast against the blue monitor glow
- Add a subtle dark gradient strip (linear-gradient to top, rgba(0,0,0,0.45) to transparent, ~120px tall) at the bottom 12% of each panel to improve contrast for the cost labels and sub-labels without obscuring Veo footage
<!-- ANNOTATION_UPDATE_END: 55bc4d1b-a9ad-4d5b-8943-f837ef506cc8 -->

<!-- ANNOTATION_UPDATE_START: d3c8eeec-a4df-4252-b6d0-6cc545cbd050 -->
## Annotation Update
Requested change: The frame is sampled at 83.3% progress (frame 199/240), deep within the peak-glow hold phase (frames 160-240). Core composition is correct: triangle centered with three correctly-colored nodes (blue top, amber bottom-left, green bottom-right), ghost code lines barely visible inside the triangle, thesis text 'The code is just plastic.' visible and centered below with horizontal rule above it, dark background. However, the multi-layer glow effects on triangle edges and node outer glows are signifi
Technical assessment: Frame 199/240 is in the peak-glow hold phase (frames 160-240), described as the 'emotional peak of the video.' The core composition is structurally correct: triangle geometry, node positions, node colors, ghost code lines, thesis text with horizontal rule, and dark background all match spec. However, several specified visual effects are significantly deficient: (1) Multi-layer glow on triangle edges (3 layers at 8px/20px/40px blur) is absent — edges render as thin wireframe lines instead of luminous halos. (2) Node outer glows (30px radius, 0.12 opacity) are missing — nodes appear as simple filled circles without radiant color emission. (3) Node labels ('PROMPT', 'TESTS', 'GROUNDING') and their descriptors should persist from previous beats but are completely absent from the frame. (4) The upward-drifting particle field (30-40 particles in blue/amber/green) is not visible. (5) Edge color should have brightened to #E2E8F0 at 0.8 opacity with 3px width; current edges appear thin and muted. The missing node labels are a compositional omission (viewers cannot identify what each vertex represents), elevating this beyond a purely decorative concern. The missing glow effects undermine the spec's core dramatic intent — contrasting the radiant mold against the fading code.
- Add multi-layer glow effects to triangle edges: 8px blur (#E2E8F0 at 0.08), 20px blur (#E2E8F0 at 0.03), and 40px blur (#475569 at 0.02) using CSS box-shadow or SVG filter chains
- Add 30px outer glow to each node circle using radial gradient or box-shadow in its signature color at 0.12 opacity
- Restore node labels ('PROMPT', 'TESTS', 'GROUNDING') and descriptors ('Encodes intent', 'Preserve behavior', 'Maintains style') which should persist from the previous beat (section 7.4)
- Brighten edge stroke to #E2E8F0 at 0.8 opacity and increase width to 3px for the peak-glow phase
- Implement the upward-drifting particle field with 30-40 particles in blue/amber/green at 0.06-0.1 opacity spawning from y:700-1080
<!-- ANNOTATION_UPDATE_END: d3c8eeec-a4df-4252-b6d0-6cc545cbd050 -->
