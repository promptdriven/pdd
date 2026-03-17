[title:]

# Section 6.1: Where to Start — Section Title Card

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 23:15 - 23:19

## Visual Description

A clean section title card introduces the final practical section. "Where to Start" appears in large white text, centered, with a subtle underline accent in blue (#4A90D9). The subtitle "Part 6" sits above in small muted type. A simple icon — a single module block with a forward-pointing play triangle — materializes to the left of the title, pulsing once with a golden glow to suggest "begin here." The icon reinforces the actionable, practical tone of this section: you're not theorizing anymore — you're starting.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none

### Chart/Visual Elements

#### Part Label
- "PART 6" — Inter, 12px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Position: centered at (960, 400)

#### Title Text
- "Where to Start" — Inter, 64px, bold (700), `#FFFFFF`
- Position: centered at (960, 480)

#### Accent Underline
- Horizontal line beneath title, 180px wide, 3px tall
- Color: `#4A90D9` at 0.7
- Centered at (960, 520)

#### Module Icon
- Position: (760, 478), 48x48px
- Module block: rounded rectangle 40x40, `#1E293B` stroke 2px `#334155`
- Play triangle: 14px equilateral, `#FBBF24`, centered within module block
- Glow pulse: 16px Gaussian blur, `#FBBF24` at 0.2, pulses once

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Background fades in from black. "PART 6" label fades in.
2. **Frame 20-50 (0.67-1.67s):** "Where to Start" title scales from 0.9→1.0 and fades in. Accent underline draws left-to-right.
3. **Frame 50-75 (1.67-2.5s):** Module icon materializes with soft pop. Play triangle fills in. Golden glow pulse fires once (expand → contract).
4. **Frame 75-120 (2.5-4s):** Hold on complete card. Subtle ambient glow on icon.

### Typography
- Part label: Inter, 12px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title: Inter, 64px, bold (700), `#FFFFFF`

### Easing
- Label fade: `easeOut(quad)` over 20 frames
- Title scale+fade: `easeOut(cubic)` over 25 frames
- Underline draw: `easeInOut(cubic)` over 20 frames
- Icon pop: `easeOut(back(1.4))` over 18 frames
- Glow pulse: `easeInOut(sine)` scale 1.0→1.3→1.0, 20 frames

## Narration Sync
> "PDD can create prompts from existing code."

Segment: `where_to_start_001`

- **23:15** ("PDD can create prompts"): Title card visible — sets context before the workflow begins

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Part label */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <Text text="PART 6" font="Inter" size={12}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title */}
    <Sequence from={20}>
      <ScaleFadeIn from={0.9} to={1.0} duration={25}>
        <Text text="Where to Start" font="Inter" size={64}
          weight={700} color="#FFFFFF"
          x={960} y={480} align="center" />
      </ScaleFadeIn>
    </Sequence>

    {/* Accent underline */}
    <Sequence from={25}>
      <LineDraw from={[870, 520]} to={[1050, 520]}
        color="#4A90D9" opacity={0.7} width={3} duration={20} />
    </Sequence>

    {/* Module icon with play triangle */}
    <Sequence from={50}>
      <ScaleIn easing="easeOut(back(1.4))" duration={18}>
        <ModuleIcon x={760} y={478} size={48}
          bgColor="#1E293B" borderColor="#334155"
          triangleColor="#FBBF24" />
      </ScaleIn>
      <Sequence from={18}>
        <GlowPulse color="#FBBF24" blur={16} opacity={0.2}
          scale={[1.0, 1.3, 1.0]} duration={20} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "cardId": "where_to_start_title",
  "sectionNumber": 6,
  "title": "Where to Start",
  "subtitle": "PART 6",
  "icon": "module_play",
  "accentColor": "#4A90D9",
  "glowColor": "#FBBF24",
  "backgroundColor": "#0F172A",
  "narrationSegments": ["where_to_start_001"]
}
```

---
