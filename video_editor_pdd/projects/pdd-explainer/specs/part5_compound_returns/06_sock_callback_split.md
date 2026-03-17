[split:]

# Section 5.6: Sock Callback — Split Screen Emotional Payoff

**Tool:** Split
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 21:58 - 22:10

## Visual Description

A vertical split screen delivers the emotional payoff of the sock metaphor. LEFT panel shows the 1960s grandmother from the cold open — but now she sets down her darning needle, looks at a new pack of socks, and reaches for them instead. RIGHT panel shows a modern developer — but now they close Cursor's diff view, and open a clean prompt file with `pdd generate` visible in the terminal. Both figures make the same realization simultaneously: the economics changed.

The left side has a warm amber lamplight grade. The right side has a cool blue-white monitor glow. Both halves carry embedded Veo clips for the live-action feel, but the split-screen framing and text overlays are Remotion-controlled.

Below the split, narration text appears as a subtitle: the grandmother's economic rationality mirrored in the developer's.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.2

### Chart/Visual Elements

#### Panel Headers
- LEFT: "1960" — Inter, 14px, semi-bold (600), `#D9944A` at 0.4, letter-spacing 2px, centered at y: 40
- RIGHT: "NOW" — Inter, 14px, semi-bold (600), `#4A90D9` at 0.4, letter-spacing 2px, centered at y: 40

#### Left Panel — Grandmother (x: 0 to x: 958)
- Background: warm amber grade over Veo clip
- Veo clip placeholder: grandmother's hands setting down darning needle, reaching for packaged socks
- Color grade overlay: `#D4A043` at 0.04, warm sepia tone
- Subtle vignette: radial gradient, edges darkened to `#0A0500` at 0.3
- Bottom caption: "The economics made it rational." — Inter, 13px, italic, `#E2E8F0` at 0.6, centered at y: 920
- Small darning needle icon (crossed out with thin line), `#D9944A` at 0.3, at (200, 900)

#### Right Panel — Developer (x: 962 to x: 1920)
- Background: cool blue grade over Veo clip
- Veo clip placeholder: developer's hands closing diff view, typing `pdd generate` in terminal
- Color grade overlay: `#4A90D9` at 0.03, cool blue tone
- Subtle vignette: radial gradient, edges darkened to `#000510` at 0.3
- Bottom caption: "Until now, the economics made it rational." — Inter, 13px, italic, `#E2E8F0` at 0.6, centered at y: 920
- Small patch icon (crossed out with thin line), `#4A90D9` at 0.3, at (1680, 900)

#### Transition Moment
- At the midpoint, both panels briefly brighten — a shared "realization" moment
- Brightness flash: 0.0 → 0.03 → 0.0 over 20 frames, white overlay
- The split line briefly glows: `#E2E8F0` at 0.15 for 10 frames

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers "1960" and "NOW" fade in.
2. **Frame 20-60 (0.67-2s):** Left panel: Veo clip plays — grandmother's hands visible, darning needle in use. Warm amber grade.
3. **Frame 60-120 (2-4s):** Left panel: grandmother sets down needle. Right panel simultaneously: developer has Cursor open with a messy diff.
4. **Frame 120-180 (4-6s):** Left panel: grandmother reaches for new sock pack. Right panel: developer closes diff view, opens prompt file.
5. **Frame 180-200 (6-6.67s):** Shared "realization" flash. Both panels brighten briefly. Split line glows.
6. **Frame 200-260 (6.67-8.67s):** Left caption fades in: "The economics made it rational." Right caption: "Until now, the economics made it rational."
7. **Frame 260-300 (8.67-10s):** Crossed-out icons appear — darning needle (left), patch icon (right).
8. **Frame 300-360 (10-12s):** Hold on complete split.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors at 0.4, letter-spacing 2px
- Bottom captions: Inter, 13px, italic, `#E2E8F0` at 0.6
- "Until now" emphasized: `#4A90D9` at 0.8

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Panel header fade: `easeOut(quad)` over 15 frames
- Realization flash: `easeOut(quad)` brightness up, `easeIn(quad)` brightness down
- Caption fade: `easeOut(quad)` over 20 frames
- Icon appear: `easeOut(cubic)` scale 0→1, 15 frames

## Narration Sync
> "Your great-grandmother wasn't stupid for darning socks. The economics made it rational."
> "And you're not stupid for patching code. Until now, the economics made it rational."

Segment: `part5_006`

- **21:58** ("Your great-grandmother wasn't stupid"): Left panel active, grandmother darning
- **22:02** ("The economics made it rational"): Left caption appears
- **22:04** ("And you're not stupid for patching code"): Right panel active, developer with diff
- **22:08** ("Until now, the economics made it rational"): Right caption appears, realization flash

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — 1960s grandmother */}
    <Panel x={0} width={958}>
      <VeoClip clipId="grandmother_callback"
        src="/clips/grandmother_callback.mp4" fit="cover" />
      <ColorGrade color="#D4A043" opacity={0.04} />
      <Vignette edgeColor="#0A0500" edgeOpacity={0.3} />
      <PanelHeader text="1960" color="#D9944A"
        opacity={0.4} letterSpacing={2} y={40} />
      <Sequence from={200}>
        <FadeIn duration={20}>
          <Text text="The economics made it rational."
            font="Inter" size={13} color="#E2E8F0"
            opacity={0.6} italic x={479} y={920} align="center" />
        </FadeIn>
      </Sequence>
      <Sequence from={260}>
        <ScaleIn duration={15}>
          <CrossedOutIcon icon="darning_needle"
            color="#D9944A" opacity={0.3} position={[200, 900]} />
        </ScaleIn>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.2} drawDuration={15} />

    {/* Realization flash */}
    <Sequence from={180}>
      <FlashOverlay color="#FFFFFF" peakOpacity={0.03}
        rampUp={10} rampDown={10} />
      <GlowLine x={960} color="#E2E8F0" peakOpacity={0.15}
        duration={10} />
    </Sequence>

    {/* Right panel — Modern developer */}
    <Panel x={962} width={958}>
      <VeoClip clipId="developer_callback"
        src="/clips/developer_callback.mp4" fit="cover" />
      <ColorGrade color="#4A90D9" opacity={0.03} />
      <Vignette edgeColor="#000510" edgeOpacity={0.3} />
      <PanelHeader text="NOW" color="#4A90D9"
        opacity={0.4} letterSpacing={2} y={40} />
      <Sequence from={200}>
        <FadeIn duration={20}>
          <RichText font="Inter" size={13} color="#E2E8F0"
            opacity={0.6} italic x={1441} y={920} align="center">
            <Span opacity={0.6}>Until now, </Span>
            <Span color="#4A90D9" opacity={0.8}>the economics made it rational.</Span>
          </RichText>
        </FadeIn>
      </Sequence>
      <Sequence from={260}>
        <ScaleIn duration={15}>
          <CrossedOutIcon icon="patch"
            color="#4A90D9" opacity={0.3} position={[1680, 900]} />
        </ScaleIn>
      </Sequence>
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
    "label": "1960",
    "content": "grandmother_callback_veo",
    "colorGrade": { "color": "#D4A043", "opacity": 0.04 },
    "caption": "The economics made it rational.",
    "crossedOutIcon": "darning_needle",
    "background": "#000000"
  },
  "rightPanel": {
    "label": "NOW",
    "content": "developer_callback_veo",
    "colorGrade": { "color": "#4A90D9", "opacity": 0.03 },
    "caption": "Until now, the economics made it rational.",
    "crossedOutIcon": "patch",
    "background": "#000000"
  },
  "sharedMoment": {
    "type": "realization_flash",
    "frame": 180,
    "peakOpacity": 0.03
  },
  "embeddedVeoClips": ["grandmother_callback", "developer_callback"],
  "backgroundColor": "#000000",
  "narrationSegments": ["part5_006"]
}
```

---
