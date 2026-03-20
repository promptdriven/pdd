[title:]

# Section 7.9: Final Title Card — Call to Action

**Tool:** Title
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 25:09 - 25:17

## Visual Description

The closing title card. The glowing triangle from the previous beat fades to a ghost watermark — barely visible, a memory. The screen settles to near-black. Then, clean typography fades in:

"Prompt-Driven Development" — the title, large and unhurried.

Below it, a terminal-style command block appears with two lines:
```
$ uv tool install pdd-cli
$ pdd update your_module.py
```
These are the viewer's next steps — practical, concrete, copy-pasteable.

Below the commands, a URL: "pdd.dev" — the single destination.

The ghost triangle watermark sits behind everything, barely perceptible — you'd only notice it if you knew to look. It connects this end card to the visual thesis: even the title card is shaped by the mold.

The delivery is quiet, unhurried, confident. No flashy CTA graphics. No "like and subscribe." Just: here's what it is, here's how to start.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#060A12` (near-black, continuous)
- No grid, no glow, no particles — clean

### Chart/Visual Elements

#### Ghost Triangle Watermark
- Same geometry: centered (960, 520), vertices at (960, 280), (710, 713), (1210, 713)
- Edge stroke: 1px, `#1E293B` at 0.04 — barely visible
- Nodes: 8px radius, respective colors at 0.02 — ghost dots
- No labels, no text — pure geometric watermark
- Positioned behind all text elements (z-index lowest)

#### Title
- "Prompt-Driven Development" — Inter, 48px, bold (700), `#E2E8F0` at 0.85
- Position: centered at (960, 380)
- Letter-spacing: 1px

#### Command Block
- Background: `#0F172A` at 0.4, rounded 8px, padding 24px 32px
- Position: centered at (960, 520), width: 480px
- Line 1: `$ uv tool install pdd-cli` — JetBrains Mono, 15px, `#E2E8F0` at 0.7
- Line 2: `$ pdd update your_module.py` — JetBrains Mono, 15px, `#E2E8F0` at 0.7
- `$` prompt character: `#64748B` at 0.4
- `pdd` keyword: `#4A90D9` at 0.8
- Line spacing: 28px between lines
- Subtle left border: 2px, `#4A90D9` at 0.15

#### URL
- "pdd.dev" — Inter, 20px, semi-bold (600), `#4A90D9` at 0.6
- Position: centered at (960, 660)
- Subtle underline: 1px, `#4A90D9` at 0.1

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous triangle fades to ghost watermark. Thesis text fades out. Screen settles to near-black with ghost triangle barely visible.
2. **Frame 30-70 (1-2.33s):** Title "Prompt-Driven Development" fades in. Clean, centered, unhurried.
3. **Frame 70-120 (2.33-4s):** Command block fades in. Background card first, then Line 1 types in character by character, then Line 2.
4. **Frame 120-150 (4-5s):** URL "pdd.dev" fades in below commands.
5. **Frame 150-240 (5-8s):** Hold. Everything visible. Ghost triangle watermark barely perceptible behind. Clean, still, confident.

### Typography
- Title: Inter, 48px, bold (700), `#E2E8F0` at 0.85, letter-spacing 1px
- Command text: JetBrains Mono, 15px, `#E2E8F0` at 0.7
- Prompt `$`: JetBrains Mono, 15px, `#64748B` at 0.4
- `pdd` keyword: JetBrains Mono, 15px, `#4A90D9` at 0.8
- URL: Inter, 20px, semi-bold (600), `#4A90D9` at 0.6

### Easing
- Triangle to ghost: `easeIn(quad)` over 25 frames
- Title fade-in: `easeOut(quad)` over 25 frames
- Command block background fade: `easeOut(quad)` over 15 frames
- Command line type: `linear`, 2 frames per character
- URL fade: `easeOut(quad)` over 18 frames

## Narration Sync
> (No narration — or quiet, unhurried delivery:)
> "Prompt-Driven Development."

Segment: `closing_008`

- **25:09** (transition): Triangle fades to ghost watermark
- **25:11** ("Prompt-Driven Development"): Title appears
- **25:13** (visual: commands appear): Install and usage commands type in
- **25:15** (visual: URL appears): "pdd.dev" fades in
- **25:17** (hold): End card complete — fade to black follows

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#060A12' }}>
    {/* Ghost triangle watermark — behind everything */}
    <TriangleFrame vertices={[[960,280],[710,713],[1210,713]]}
      edgeColor="#1E293B" edgeOpacity={0.04} edgeWidth={1}>
      <NodeCircle center={[960, 280]} radius={8}
        fill="#4A90D9" opacity={0.02} />
      <NodeCircle center={[710, 713]} radius={8}
        fill="#D9944A" opacity={0.02} />
      <NodeCircle center={[1210, 713]} radius={8}
        fill="#5AAA6E" opacity={0.02} />
    </TriangleFrame>

    {/* Title */}
    <Sequence from={30}>
      <FadeIn duration={25}>
        <Text text="Prompt-Driven Development"
          font="Inter" size={48} weight={700}
          color="#E2E8F0" opacity={0.85}
          letterSpacing={1}
          x={960} y={380} align="center" />
      </FadeIn>
    </Sequence>

    {/* Command block */}
    <Sequence from={70}>
      <FadeIn duration={15}>
        <CommandCard x={960} y={520} width={480}
          padding={[24, 32]} bgColor="#0F172A" bgOpacity={0.4}
          borderRadius={8} borderLeft={{ width: 2, color: '#4A90D9', opacity: 0.15 }}>
          <TerminalLine delay={0}>
            <Span color="#64748B" opacity={0.4}>$ </Span>
            <Span color="#E2E8F0" opacity={0.7}>uv tool install </Span>
            <Span color="#4A90D9" opacity={0.8}>pdd-cli</Span>
          </TerminalLine>
          <TerminalLine delay={20}>
            <Span color="#64748B" opacity={0.4}>$ </Span>
            <Span color="#4A90D9" opacity={0.8}>pdd</Span>
            <Span color="#E2E8F0" opacity={0.7}> update your_module.py</Span>
          </TerminalLine>
        </CommandCard>
      </FadeIn>
    </Sequence>

    {/* URL */}
    <Sequence from={120}>
      <FadeIn duration={18}>
        <Text text="pdd.dev"
          font="Inter" size={20} weight={600}
          color="#4A90D9" opacity={0.6}
          x={960} y={660} align="center" />
        <Line from={[920, 674]} to={[1000, 674]}
          color="#4A90D9" opacity={0.1} width={1} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "cardId": "final_title_card",
  "title": "Prompt-Driven Development",
  "commands": [
    "uv tool install pdd-cli",
    "pdd update your_module.py"
  ],
  "url": "pdd.dev",
  "ghostTriangle": {
    "edgeOpacity": 0.04,
    "nodeOpacity": 0.02
  },
  "backgroundColor": "#060A12",
  "narrationSegments": ["closing_008"]
}
```

---

<!-- ANNOTATION_UPDATE_START: 627b0945-b7bd-4ef2-a0d2-ab5494a30f97 -->
## Annotation Update
Requested change: The frame is sampled at 91.7% progress (frame 219/240), which falls in animation phase 6 (frame 200-240: 'Hold on complete split'). At this point the spec requires the complete split view with cost labels, sub-labels, and panel headers all fully visible. Assessment of visible elements:

1. **Split layout**: PASS — Vertical split is present with left and right panels roughly divided at center. The divider line between panels is visible.
2. **Left panel content**: PASS — Shows hands holding a pack
Technical assessment: Frame 219/240 (phase 6: 'Hold on complete split') is missing panel headers and sub-labels, and cost labels are undersized. The spec requires: (1) 'DISCARD' and 'REGENERATE' headers at y:36 in Inter 12px semi-bold with letter-spacing 3px — these are completely absent; (2) cost labels '$2' and '~30s' at Inter 28px bold at opacity 0.7 — these are present but appear significantly undersized, likely rendered at a smaller font size than the specified 28px; (3) sub-labels 'new pair' and 'regenerated' at y:990 in Inter 11px — these are not visible. The Veo clip content, split layout, color grading, vignettes, and background are all correct. All missing/undersized elements are Remotion text overlays.
- Add PanelHeader components for 'DISCARD' (color #D9944A, opacity 0.3, y:36) and 'REGENERATE' (color #4A90D9, opacity 0.3, y:36) with Inter 12px semi-bold and letter-spacing 3px
- Increase cost label font size to the specified 28px bold (Inter) at opacity 0.7 — '$2' centered in left panel at y:960, '~30s' centered in right panel at y:960
- Add sub-label text overlays: 'new pair' (left, y:990) and 'regenerated' (right, y:990) in Inter 11px, color #94A3B8 at opacity 0.4
- Verify the terminal snippet 'pdd bug → pdd fix → ✓' is rendering at position (1780, 1020) in JetBrains Mono 10px
<!-- ANNOTATION_UPDATE_END: 627b0945-b7bd-4ef2-a0d2-ab5494a30f97 -->
