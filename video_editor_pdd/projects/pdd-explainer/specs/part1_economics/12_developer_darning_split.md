[split:]

# Section 1.12: Developer Darning Split — Cursor & the Darning Needle

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 5:20 - 5:34

## Visual Description

A vertical split screen for the metaphor payoff. LEFT panel: a developer working efficiently with Cursor — code flying, suggestions accepted, the productive flow of modern AI-assisted coding. This is respectful, not dismissive. RIGHT panel: a grandmother darning a sock with expert skill — steady hands, focused work, equally competent.

Both halves show skilled craftspeople using excellent tools. The point isn't that either is bad — it's what comes next.

On the developer's side, the camera "zooms out" revealing the codebase is massive and tangled. Code comments appear: "// don't touch this", "// legacy", "// temporary fix (2019)". The darning needle metaphor becomes concrete: the tool is great, but the accumulated material is the problem.

The left panel embeds a Veo clip of developer hands coding. The right panel embeds a Veo clip of hands darning. Companion [veo:] specs generate these clips.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.2

### Chart/Visual Elements

#### Panel Headers
- LEFT: "CURSOR" — Inter, 14px, semi-bold (600), `#4A90D9` at 0.4, letter-spacing 2px, centered at y: 40
- RIGHT: "DARNING NEEDLE" — Inter, 14px, semi-bold (600), `#D9944A` at 0.4, letter-spacing 2px, centered at y: 40

#### Left Panel — Developer with Cursor (x: 0 to x: 958)
- Background: cool blue grade over Veo clip
- Veo clip: developer's hands on keyboard, Cursor IDE visible with code suggestions
- Color grade: `#4A90D9` at 0.03, cool blue
- Subtle vignette: radial, edges to `#000510` at 0.3

#### Right Panel — Grandmother Darning (x: 962 to x: 1920)
- Background: warm amber grade over Veo clip
- Veo clip: grandmother's hands expertly darning a wool sock under lamplight
- Color grade: `#D4A043` at 0.04, warm amber
- Subtle vignette: radial, edges to `#0A0500` at 0.3

#### Zoom-Out Code Comments (appear on left panel, frame 240+)
- The Veo clip fades to 0.3 opacity
- Faux code overlay appears:
  - "// don't touch this" — JetBrains Mono, 11px, `#EF4444` at 0.6, at y: 300
  - "// legacy" — JetBrains Mono, 11px, `#EF4444` at 0.6, at y: 450
  - "// temporary fix (2019)" — JetBrains Mono, 11px, `#EF4444` at 0.6, at y: 600
- Tangled dependency lines: thin 1px curves connecting code blocks, `#475569` at 0.2

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-120 (0.67-4s):** Both Veo clips play simultaneously. Developer typing efficiently. Grandmother darning with skill. Both look competent.
3. **Frame 120-240 (4-8s):** Hold on the parallel. Narration emphasizes respect for both tools.
4. **Frame 240-320 (8-10.67s):** Left panel: Veo clip dims. Code comment overlays appear one by one. Tangled dependency lines draw in.
5. **Frame 320-420 (10.67-14s):** Hold on the revealed mess. Right panel grandmother continues calmly. The contrast speaks for itself.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors at 0.4, letter-spacing 2px
- Code comments: JetBrains Mono, 11px, `#EF4444` at 0.6

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Header fade: `easeOut(quad)` over 15 frames
- Veo clip dim: `easeOut(quad)` over 30 frames to 0.3
- Comment appear: `easeOut(quad)` staggered 20 frames each
- Dependency lines draw: `easeInOut(cubic)` over 40 frames

## Narration Sync
> "Tools like Cursor and Claude Code are the best darning needles ever made. I use them. They're fantastic."
> "But they're still darning needles. And the fundamental problem with darning isn't speed—it's accumulation."

Segments: `part1_economics_032`, `part1_economics_033`

- **5:20** ("Tools like Cursor"): Split screen shows both halves working efficiently
- **5:28** ("still darning needles"): Developer side zooms out, code comments appear
- **5:34** ("accumulation"): Hold on tangled codebase reveal

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Developer */}
    <Panel x={0} width={958}>
      <VeoClip clipId="developer_cursor_coding"
        src="/clips/developer_cursor_coding.mp4" fit="cover" />
      <ColorGrade color="#4A90D9" opacity={0.03} />
      <Vignette edgeColor="#000510" edgeOpacity={0.3} />
      <PanelHeader text="CURSOR" color="#4A90D9"
        opacity={0.4} letterSpacing={2} y={40} />

      {/* Zoom-out code overlay */}
      <Sequence from={240}>
        <FadeIn duration={30}>
          <Overlay opacity={0.7} color="#0A0F1A" />
        </FadeIn>
        <StaggeredFadeIn stagger={20}>
          <CodeComment text="// don't touch this"
            font="JetBrains Mono" size={11}
            color="#EF4444" opacity={0.6} y={300} />
          <CodeComment text="// legacy"
            font="JetBrains Mono" size={11}
            color="#EF4444" opacity={0.6} y={450} />
          <CodeComment text="// temporary fix (2019)"
            font="JetBrains Mono" size={11}
            color="#EF4444" opacity={0.6} y={600} />
        </StaggeredFadeIn>
        <TangledLines connections={dependencyGraph}
          color="#475569" opacity={0.2} drawDuration={40} />
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.2} drawDuration={15} />

    {/* Right panel — Grandmother */}
    <Panel x={962} width={958}>
      <VeoClip clipId="grandmother_darning_expert"
        src="/clips/grandmother_darning_expert.mp4" fit="cover" />
      <ColorGrade color="#D4A043" opacity={0.04} />
      <Vignette edgeColor="#0A0500" edgeOpacity={0.3} />
      <PanelHeader text="DARNING NEEDLE" color="#D9944A"
        opacity={0.4} letterSpacing={2} y={40} />
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
    "label": "CURSOR",
    "content": "developer_cursor_coding",
    "colorGrade": { "color": "#4A90D9", "opacity": 0.03 },
    "codeComments": [
      "// don't touch this",
      "// legacy",
      "// temporary fix (2019)"
    ],
    "background": "#000000"
  },
  "rightPanel": {
    "label": "DARNING NEEDLE",
    "content": "grandmother_darning_expert",
    "colorGrade": { "color": "#D4A043", "opacity": 0.04 },
    "background": "#000000"
  },
  "embeddedVeoClips": ["developer_cursor_coding", "grandmother_darning_expert"],
  "backgroundColor": "#000000",
  "narrationSegments": ["part1_economics_032", "part1_economics_033"]
}
```

---
