[Remotion]

# Section 6.6: No Big Bang Callout — Gradual Migration Text Card

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:22 - 0:28

## Visual Description

A text-forward infographic that reinforces the "no big bang" message. The module grid from the previous spec is still faintly visible in the background (8/20 glowing), but heavily blurred and dimmed to ~0.15 opacity — it becomes atmospheric.

Three short statements appear in sequence, stacked vertically, center-screen:

1. **"No big bang."** — appears first, bold, white
2. **"No rewrite."** — appears second, bold, white
3. **"Just a gradual migration of where value lives."** — appears third, slightly smaller, with "value" highlighted in blue-purple

Each line enters with a clean left-to-right wipe, timed to the narration cadence. The three lines together form a manifesto-style layout — minimal, confident, declarative.

Below the three lines, a subtle animated graphic: a horizontal bar that transitions from gray (code) on the left to glowing purple (prompt) on the right, with the transition point slowly sliding rightward — a visual metaphor for the gradual migration.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Background layer: blurred module grid from Spec 05 at 0.15

### Chart/Visual Elements

#### Statement Lines
| Line | Text | Font | Size | Weight | Color | Position (y) |
|------|------|------|------|--------|-------|--------------|
| 1 | "No big bang." | Inter | 42px | Bold (700) | `#E2E8F0` | 380 |
| 2 | "No rewrite." | Inter | 42px | Bold (700) | `#E2E8F0` | 440 |
| 3 | "Just a gradual migration of where value lives." | Inter | 28px | Regular (400) | `#94A3B8` | 520 |

- Line 3 highlight: "value" rendered in `#8B5CF6` at 1.0, semi-bold (600)
- All lines left-aligned at x: 500, right margin comfortable
- Line spacing: 60px between lines 1-2, 80px between lines 2-3

#### Migration Bar
- Position: centered at y: 640, width: 600px, height: 6px, rounded ends
- Left portion: `#475569` (code/gray)
- Right portion: `#8B5CF6` (prompt/purple), with soft glow
- Transition point: animated, sliding from 20% to 50% over hold period
- Small labels: "code" (left end, `#475569`), "specification" (right end, `#8B5CF6`) — Inter, 11px

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Blurred module grid background stabilizes. Frame settles.
2. **Frame 20-50 (0.67-1.67s):** Line 1 "No big bang." wipes in from left. Clean, decisive.
3. **Frame 50-80 (1.67-2.67s):** Line 2 "No rewrite." wipes in.
4. **Frame 80-120 (2.67-4s):** Line 3 wipes in. "value" highlights in purple.
5. **Frame 120-140 (4-4.67s):** Migration bar fades in below. Transition point starts at 20%.
6. **Frame 140-180 (4.67-6s):** Migration bar transition slides rightward to 50%. Labels appear. Hold.

### Typography
- Lines 1-2: Inter, 42px, bold (700), `#E2E8F0`
- Line 3: Inter, 28px, regular (400), `#94A3B8`, with "value" in `#8B5CF6` semi-bold (600)
- Bar labels: Inter, 11px, respective colors at 0.6

### Easing
- Line wipe-in: `easeOut(cubic)` over 20 frames, masked left-to-right reveal
- "value" highlight: `easeOut(quad)` color transition over 10 frames
- Migration bar fade-in: `easeOut(quad)` over 15 frames
- Bar transition slide: `easeInOut(quad)` over 40 frames (20% → 50%)

## Narration Sync
> "One module at a time. No big bang. No rewrite. Just a gradual migration of where value lives — from code to specification."

Segment: `where_to_start_002` (closing beats)

- **0:22** (22.00s): "No big bang." appears
- **0:23** (23.00s): "No rewrite." appears
- **0:24** (24.00s): "Just a gradual migration..." appears
- **0:26** (26.24s): Migration bar visible, hold — segment ends

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Blurred background: module grid from Spec 05 */}
    <BlurLayer blur={20} opacity={0.15}>
      <ModuleGrid converted={8} total={20} />
    </BlurLayer>

    {/* Statement lines */}
    <Sequence from={20}>
      <WipeReveal direction="left-to-right" duration={20}>
        <Text text="No big bang." font="Inter" size={42}
          weight={700} color="#E2E8F0"
          x={500} y={380} align="left" />
      </WipeReveal>
    </Sequence>

    <Sequence from={50}>
      <WipeReveal direction="left-to-right" duration={20}>
        <Text text="No rewrite." font="Inter" size={42}
          weight={700} color="#E2E8F0"
          x={500} y={440} align="left" />
      </WipeReveal>
    </Sequence>

    <Sequence from={80}>
      <WipeReveal direction="left-to-right" duration={25}>
        <RichText x={500} y={520} align="left" font="Inter" size={28}>
          <Span color="#94A3B8" weight={400}>
            Just a gradual migration of where{' '}
          </Span>
          <Span color="#8B5CF6" weight={600}>value</Span>
          <Span color="#94A3B8" weight={400}> lives.</Span>
        </RichText>
      </WipeReveal>
    </Sequence>

    {/* Migration bar */}
    <Sequence from={120}>
      <FadeIn duration={15}>
        <MigrationBar
          x={660} y={640} width={600} height={6}
          leftColor="#475569" rightColor="#8B5CF6"
          initialSplit={0.2} finalSplit={0.5}
          transitionStart={20} transitionDuration={40}
          leftLabel="code" rightLabel="specification"
          labelFont="Inter" labelSize={11}
          rounded
        />
      </FadeIn>
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "text_manifesto",
  "statements": [
    { "text": "No big bang.", "frame": 20, "style": "bold" },
    { "text": "No rewrite.", "frame": 50, "style": "bold" },
    { "text": "Just a gradual migration of where value lives.", "frame": 80, "highlight": "value" }
  ],
  "migrationBar": {
    "from": "code",
    "to": "specification",
    "startSplit": 0.2,
    "endSplit": 0.5,
    "leftColor": "#475569",
    "rightColor": "#8B5CF6"
  },
  "narrationSegments": ["where_to_start_002"]
}
```

---
