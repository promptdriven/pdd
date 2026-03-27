[Remotion]

# Section 3.10: Z3 Formal Proof — Sidebar Annotation

**Tool:** Remotion
**Duration:** ~26s (780 frames @ 30fps)
**Timestamp:** 3:02 - 3:28

## Visual Description

A brief sidebar annotation overlaid on the mold diagram. The annotation panel slides in from the right side of the screen, occupying roughly a third of the canvas width.

The annotation contains:
- Main text: "PDD also uses Z3 — the same class of SMT solver used in chip verification — to formally prove properties hold for every possible input."
- Emphasis line: "Same math as billion-dollar tapeouts."
- Two small logos side by side: a stylized "Z3" icon and a Synopsys Formality-style icon, both rendered as clean SVG-style badges.

Behind the annotation, the mold from previous shots remains visible at reduced opacity, with certain wall segments highlighted to indicate "proven" constraints (these walls have a purple glow instead of blue, signifying formal verification rather than testing).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Mold visible at 0.3 opacity on left side

### Chart/Visual Elements

#### Annotation Panel
- Position: right side, x: 1000 to 1840, y: 200 to 780
- Background: `#0F172A` at 0.95, border `#334155` 1px, rounded 12px
- Inner padding: 32px

#### Text Content
- Main text: Inter, 16px, regular (400), `#CDD6F4`, line-height 1.6
- "Z3" inline: bold (700), `#A78BFA` (purple)
- "SMT solver" inline: bold (700), `#A78BFA`
- "formally prove" inline: bold (700), `#A78BFA`
- Emphasis: "Same math as billion-dollar tapeouts." — Inter, 18px, semi-bold (600), `#E2E8F0`
- "Not sampling. Mathematical proof." — Inter, 16px, italic, `#A78BFA` at 0.8

#### Logo Badges
- Z3: 48×48px badge, `#A78BFA` fill, rounded 8px, "Z3" in white bold
- Synopsys Formality style: 48×48px badge, `#7C3AED` fill, rounded 8px, "SF" in white bold
- Positioned at bottom of annotation panel, 24px apart, centered

#### Mold Proven Walls
- 2-3 wall segments on the left-side mold glow purple (`#A78BFA` at 0.3) instead of blue
- Connector lines from annotation to proven walls, `#A78BFA` at 0.2, dashed

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold dims to 0.3 opacity. Annotation panel slides in from right (translateX 300px → 0).
2. **Frame 30-90 (1-3s):** Main text types in word by word (fast, ~3 frames per word). "Z3", "SMT solver", "formally prove" appear in purple bold.
3. **Frame 90-150 (3-5s):** "Same math as billion-dollar tapeouts" fades in with slight scale (0.95 → 1.0).
4. **Frame 150-210 (5-7s):** "Not sampling. Mathematical proof." fades in italic.
5. **Frame 210-270 (7-9s):** Logo badges fade in side by side. Brief glow pulse.
6. **Frame 270-360 (9-12s):** Connector lines draw from annotation to 2-3 mold walls. Those walls transition from blue to purple glow.
7. **Frame 360-720 (12-24s):** Hold. Annotation visible, proven walls glowing purple.
8. **Frame 720-780 (24-26s):** Annotation panel slides out. Mold returns to full opacity. Proven walls retain purple tint.

### Typography
- Main text: Inter, 16px, regular (400), `#CDD6F4`
- Inline emphasis: Inter, 16px, bold (700), `#A78BFA`
- Pull quote: Inter, 18px, semi-bold (600), `#E2E8F0`
- Italic line: Inter, 16px, italic, `#A78BFA` at 0.8

### Easing
- Panel slide-in: `easeOut(cubic)` over 30 frames
- Text word-type: `easeOut(quad)` per word
- Emphasis scale: `easeOut(quad)` over 20 frames
- Logo fade: `easeOut(quad)` over 20 frames
- Connector draw: `easeOut(quad)` over 30 frames
- Wall color transition: `easeInOut(sine)` over 30 frames
- Panel slide-out: `easeIn(cubic)` over 30 frames

## Narration Sync
> "And some of those walls aren't just tested — they're proven. PDD uses Z3, the same class of SMT solver that the chip industry uses for formal equivalence checking, to mathematically prove that properties hold for every possible input. Not sampling. Mathematical proof. The chip design analogy isn't a metaphor. It's the same technology."

Segment: `part3_mold_parts_014`

- **181.98s** (seg 014): Annotation panel slides in — "some of those walls aren't just tested"
- **186.0s**: "Z3" appears in purple
- **192.0s**: "formally prove" — emphasis text
- **198.0s**: "Not sampling. Mathematical proof." — italic line
- **202.0s**: Logos visible, connector lines to walls
- **208.02s** (seg 014 ends): Annotation slides out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={780}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dimmed mold */}
    <div style={{ opacity: 0.3 }}>
      <MoldCrossSection wallsOpacity={0.4} />
    </div>

    {/* Annotation panel */}
    <Sequence from={0}>
      <SlideIn from="right" distance={300} duration={30}>
        <AnnotationPanel
          x={1000} y={200} width={840} height={580}
          background="#0F172A" borderColor="#334155"
          borderRadius={12} padding={32}
        >
          {/* Main text with inline highlights */}
          <Sequence from={30}>
            <WordByWord
              text={Z3_ANNOTATION_TEXT}
              highlights={[
                { word: "Z3", color: "#A78BFA", bold: true },
                { word: "SMT solver", color: "#A78BFA", bold: true },
                { word: "formally prove", color: "#A78BFA", bold: true }
              ]}
              wordDelay={3}
            />
          </Sequence>

          {/* Emphasis line */}
          <Sequence from={90}>
            <ScaleIn from={0.95} to={1.0} duration={20}>
              <FadeIn duration={20}>
                <Text text="Same math as billion-dollar tapeouts."
                  font="Inter" size={18} weight={600} color="#E2E8F0" />
              </FadeIn>
            </ScaleIn>
          </Sequence>

          {/* Italic line */}
          <Sequence from={150}>
            <FadeIn duration={20}>
              <Text text="Not sampling. Mathematical proof."
                font="Inter" size={16} italic color="#A78BFA" opacity={0.8} />
            </FadeIn>
          </Sequence>

          {/* Logo badges */}
          <Sequence from={210}>
            <FadeIn duration={20}>
              <LogoBadge text="Z3" color="#A78BFA" size={48} />
              <LogoBadge text="SF" color="#7C3AED" size={48} />
            </FadeIn>
          </Sequence>
        </AnnotationPanel>
      </SlideIn>
    </Sequence>

    {/* Connector lines + purple walls */}
    <Sequence from={270}>
      <ProvenWalls
        wallIndices={[1, 3]}
        fromColor="#4A90D9" toColor="#A78BFA"
        connectorOrigin={[1000, 500]}
        drawDuration={30}
      />
    </Sequence>

    {/* Slide out */}
    <Sequence from={720}>
      <SlideOut to="right" distance={300} duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "sidebar_annotation",
  "topic": "Z3 formal verification",
  "keyTerms": ["Z3", "SMT solver", "formal equivalence checking", "mathematical proof"],
  "provenWalls": [1, 3],
  "provenColor": "#A78BFA",
  "logos": [
    { "text": "Z3", "color": "#A78BFA" },
    { "text": "SF", "color": "#7C3AED" }
  ],
  "narrationSegments": ["part3_mold_parts_014"],
  "durationSeconds": 26.0
}
```

---
