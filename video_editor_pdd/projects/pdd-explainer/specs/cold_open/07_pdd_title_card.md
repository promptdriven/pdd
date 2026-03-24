[title:]

# Section 0.7: PDD Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:16 - 0:18

## Visual Description

The title card that closes the cold open. Over the regenerated clean code from the previous spec, the title "Prompt-Driven Development" fades in — large, authoritative, centered. The code behind dims slightly but remains visible, establishing that PDD is about code, not theory.

The title uses the project's primary blue `#4A90D9` — the "regeneration / PDD" color — contrasting with the amber `#D9944A` that represented patching throughout the cold open. This color shift signals: we've moved from the old paradigm to the new one.

Below the title, a thin subtitle appears: the video's thesis in one line.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` at 0.85 overlay on top of the regenerated code from spec 06
- The code is visible but dimmed — title reads clearly over it

### Chart/Visual Elements

#### Code Underlay
- The clean regenerated code from spec 06 remains visible at 0.15 opacity
- Creates depth and context — this title is *about* what just happened
- Terminal overlay from spec 06 fades out during first 10 frames

#### Title Text
- "Prompt-Driven Development" — Inter, 56px, bold (700), `#4A90D9` at 0.95
- Centered horizontally (x: 960) and vertically (y: 490)
- Subtle glow: `#4A90D9` at 0.08, 20px blur radius behind text

#### Horizontal Rule
- 140px wide, 2px, `#4A90D9` at 0.25, centered at y: 545
- Draws from center outward

#### Subtitle
- "So why are we still patching?" — Inter, 18px, weight 300 (light), italic, `#94A3B8` at 0.5
- Centered at y: 575
- This echoes the narrator's final question

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Code underlay dims from full to 0.15 opacity. Terminal overlay fades out.
2. **Frame 8-28 (0.27-0.93s):** Title "Prompt-Driven Development" fades in with 12px upward slide. Glow appears simultaneously.
3. **Frame 28-38 (0.93-1.27s):** Horizontal rule draws from center outward.
4. **Frame 38-48 (1.27-1.6s):** Subtitle "So why are we still patching?" fades in.
5. **Frame 48-60 (1.6-2s):** Hold. Title sits with authority. The question hangs.

### Typography
- Title: Inter, 56px, bold (700), `#4A90D9` at 0.95
- Subtitle: Inter, 18px, light (300), italic, `#94A3B8` at 0.5

### Easing
- Code dim: `easeOut(quad)` over 8 frames
- Title fade-in + slide: `easeOut(cubic)` over 20 frames
- Rule draw: `easeOut(cubic)` over 10 frames
- Subtitle fade-in: `easeOut(quad)` over 10 frames

## Narration Sync
> "So why are we still patching?"

Segment: `cold_open_006`

- **0:16** ("So why are we"): Title fades in over dimmed code
- **0:17** ("still patching?"): Subtitle appears — the question lands, the cold open ends

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Code underlay from previous spec — dimmed */}
    <Sequence from={0}>
      <FadeOut from={0.7} to={0.15} duration={8}>
        <CodeBlock lines={newCleanCodeLines}
          font="JetBrains Mono" fontSize={14} />
      </FadeOut>
    </Sequence>

    {/* Dark overlay to ensure title readability */}
    <AbsoluteFill style={{ backgroundColor: 'rgba(13, 17, 23, 0.85)' }} />

    {/* Title */}
    <Sequence from={8}>
      <SlideUp distance={12} duration={20}>
        <FadeIn duration={20}>
          <Text text="Prompt-Driven Development"
            font="Inter" size={56} weight={700}
            color="#4A90D9" opacity={0.95}
            x={960} y={490} align="center"
            glow={{ color: '#4A90D9', opacity: 0.08, blur: 20 }} />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={28}>
      <DrawLine from={[890, 545]} to={[1030, 545]}
        color="#4A90D9" opacity={0.25} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Subtitle */}
    <Sequence from={38}>
      <FadeIn duration={10}>
        <Text text="So why are we still patching?"
          font="Inter" size={18} weight={300}
          fontStyle="italic"
          color="#94A3B8" opacity={0.5}
          x={960} y={575} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 0,
  "sectionLabel": "Cold Open",
  "title": "Prompt-Driven Development",
  "titleColor": "#4A90D9",
  "subtitle": "So why are we still patching?",
  "subtitleColor": "#94A3B8",
  "backgroundColor": "#0D1117",
  "codeUnderlay": true,
  "underlayOpacity": 0.15,
  "narrationSegments": ["cold_open_006"]
}
```

---
