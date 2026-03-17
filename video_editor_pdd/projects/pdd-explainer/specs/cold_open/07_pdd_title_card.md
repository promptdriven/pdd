[title:]

# Section 0.7: PDD Title Card — The Promise

**Tool:** Title
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:33 - 0:38

## Visual Description

The question from the previous shot dissolves, and the answer materializes: "Prompt-Driven Development" fades in as a clean, authoritative title card. The title appears over the dimmed regenerated code background — visually connecting the concept to the transformation the viewer just witnessed.

The title uses the video's signature cool blue (`#4A90D9`) — the prompt color from the design palette. Below it, a thin subtitle line reads "Writing the mold, not the plastic." in lighter, smaller text. This is the thesis statement of the entire video, planted in the viewer's mind before the narrative unfolds.

In the bottom-right corner, the terminal snippet `pdd generate` remains faintly visible — a breadcrumb for developers who are already curious about the tool.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (continues from previous shots — IDE background)
- Code underlay: regenerated code at 0.04 opacity (even dimmer than previous shot)

### Chart/Visual Elements

#### Title Text
- "Prompt-Driven" — Inter, 64px, bold (700), `#4A90D9` at 0.95, centered at y: 480
- "Development" — Inter, 64px, bold (700), `#4A90D9` at 0.95, centered at y: 555
- Subtle glow: 12px Gaussian blur, `#4A90D9` at 0.08 — the prompt color glows

#### Subtitle
- "Writing the mold, not the plastic." — Inter, 18px, weight 300 (light), `#94A3B8` at 0.5, centered at y: 620
- Italic style

#### Horizontal Rule
- 160px wide, 2px, `#4A90D9` at 0.2, centered between title and subtitle at y: 590
- Draws from center outward

#### Terminal Breadcrumb
- `pdd generate` — JetBrains Mono, 10px, `#4A90D9` at 0.15, bottom-right (1800, 1040)
- Nearly invisible — discoverable, not attention-grabbing

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Previous question text ("So why are we still patching?") fades out. Code underlay dims further from 0.08 to 0.04.
2. **Frame 20-50 (0.67-1.67s):** "Prompt-Driven" fades in with a 10px upward slide. Glow appears simultaneously.
3. **Frame 50-60 (1.67-2s):** Horizontal rule draws from center outward.
4. **Frame 60-80 (2-2.67s):** "Development" fades in with a 10px upward slide.
5. **Frame 80-100 (2.67-3.33s):** Subtitle fades in. Terminal breadcrumb appears.
6. **Frame 100-150 (3.33-5s):** Hold. The title sits with authority. The glow pulses very gently — one slow cycle.

### Typography
- Title lines: Inter, 64px, bold (700), `#4A90D9` at 0.95
- Subtitle: Inter, 18px, light (300), italic, `#94A3B8` at 0.5
- Terminal breadcrumb: JetBrains Mono, 10px, `#4A90D9` at 0.15

### Easing
- Previous text fade-out: `easeIn(quad)` over 15 frames
- Title slide-up + fade-in: `easeOut(cubic)` over 25 frames
- Rule draw: `easeOut(cubic)` over 10 frames
- Subtitle fade-in: `easeOut(quad)` over 20 frames
- Glow pulse: `easeInOut(sine)` on 50-frame cycle, opacity 0.08 → 0.12 → 0.08

## Narration Sync
> (No narration — the title card speaks for itself. Transition beat before the 30-second demo.)

Segment: `cold_open_006`
Timing: 0:33 - 0:38 (silence, title card holds before Part 1 begins at ~2:00 after the 30-second demo)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Dimmed code underlay */}
    <CodeBlock
      code={regeneratedCodeLines}
      font="JetBrains Mono" size={14}
      syntaxTheme="github-dark"
      opacity={0.04}
    />

    {/* Previous question fades out */}
    <Sequence from={0} durationInFrames={20}>
      <FadeOut duration={15}>
        <Text text="So why are we still patching?"
          font="Inter" size={42} weight={300}
          color="#E2E8F0" x={960} y={540} align="center" />
      </FadeOut>
    </Sequence>

    {/* Title: Prompt-Driven */}
    <Sequence from={20}>
      <SlideUp distance={10} duration={25}>
        <FadeIn duration={25}>
          <Text text="Prompt-Driven" font="Inter" size={64}
            weight={700} color="#4A90D9" opacity={0.95}
            x={960} y={480} align="center"
            glow={{ blur: 12, color: '#4A90D9', opacity: 0.08 }} />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={50}>
      <DrawLine from={[880, 590]} to={[1040, 590]}
        color="#4A90D9" opacity={0.2} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: Development */}
    <Sequence from={60}>
      <SlideUp distance={10} duration={25}>
        <FadeIn duration={25}>
          <Text text="Development" font="Inter" size={64}
            weight={700} color="#4A90D9" opacity={0.95}
            x={960} y={555} align="center"
            glow={{ blur: 12, color: '#4A90D9', opacity: 0.08 }} />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Subtitle */}
    <Sequence from={80}>
      <FadeIn duration={20}>
        <Text text="Writing the mold, not the plastic."
          font="Inter" size={18} weight={300}
          fontStyle="italic"
          color="#94A3B8" opacity={0.5}
          x={960} y={620} align="center" />
      </FadeIn>
    </Sequence>

    {/* Terminal breadcrumb */}
    <Sequence from={80}>
      <FadeIn duration={20}>
        <TerminalSnippet text="pdd generate"
          font="JetBrains Mono" size={10}
          color="#4A90D9" opacity={0.15}
          x={1800} y={1040} />
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
  "sectionLabel": null,
  "titleLine1": "Prompt-Driven",
  "titleLine2": "Development",
  "titleColor": "#4A90D9",
  "subtitle": "Writing the mold, not the plastic.",
  "subtitleColor": "#94A3B8",
  "backgroundColor": "#0D1117",
  "codeUnderlayOpacity": 0.04,
  "glow": { "blur": 12, "color": "#4A90D9", "opacity": 0.08 },
  "terminalBreadcrumb": "pdd generate",
  "narrationSegments": ["cold_open_006"]
}
```

---
