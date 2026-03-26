[Remotion]

# Section 6.4: Source of Truth Label — Artifact vs. Source Visual Contrast

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:12 - 0:17

## Visual Description

A focused moment that crystallizes the mental model shift. The frame simplifies to show just two elements side by side, stripped of the codebase clutter:

**LEFT:** The original code file (`auth_handler.py`) — rendered as a document with grayed-out text, a dashed border, and a label stamped diagonally across it: "ARTIFACT". The label is semi-transparent, like a watermark. The document looks disposable — it can be thrown away and regenerated.

**RIGHT:** The prompt file (`auth_handler.prompt.md`) — compact, glowing with a solid blue-purple border. A label beneath reads: "SOURCE OF TRUTH". The document pulses gently, alive, authoritative.

Between them, a simple directional indicator: `generates →` pointing from prompt to code, and `extracts ←` pointing from code to prompt. This two-way relationship is the key insight.

Below both documents, a single clean line of text: "When the regenerated version passes all tests, the prompt is your new source of truth."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Code Document (Artifact)
- Rounded rectangle: 380x260px, `#1E1E2E` fill, `#475569` 2px border, dashed
- Position: x: 340, y: 300
- File label: `auth_handler.py` — JetBrains Mono, 12px, `#475569`
- Body: 6 lines of grayed-out code, JetBrains Mono, 11px, `#475569` at 0.4
- "ARTIFACT" watermark: Inter, 36px, bold, `#475569` at 0.15, rotated -15°, centered on document

#### Prompt Document (Source of Truth)
- Rounded rectangle: 380x260px, `#1E1E2E` fill, `#8B5CF6` 2px border, solid
- Position: x: 1200, y: 300
- File label: `auth_handler.prompt.md` — Inter, 12px, `#8B5CF6`
- Body: 5 lines of spec text, Inter, 12px, `#E2E8F0` at 0.8
- Glow: `#8B5CF6` at 0.1, 16px blur
- Pulse: gentle brightness oscillation

#### Directional Labels (between documents)
- "generates →" — Inter, 13px, `#4A90D9` at 0.5, positioned at y: 410
- "← extracts" — Inter, 13px, `#64748B` at 0.4, positioned at y: 440
- Small horizontal arrows accompanying each label

#### Category Labels
- Under code doc: "ARTIFACT" — Inter, 16px, semi-bold, `#475569` at 0.6, centered below
- Under prompt doc: "SOURCE OF TRUTH" — Inter, 16px, semi-bold, `#8B5CF6` at 0.8, centered below

#### Bottom Annotation
- "When the regenerated version passes all tests, the prompt is your new source of truth."
- Inter, 18px, `#E2E8F0` at 0.7, centered at y: 750
- "source of truth" portion in `#8B5CF6` at 0.9

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Background establishes. Both documents fade in simultaneously from slight inward slide (code from left, prompt from right).
2. **Frame 20-50 (0.67-1.67s):** "ARTIFACT" watermark stamps onto code document with a subtle press-down effect. Code text desaturates further.
3. **Frame 50-80 (1.67-2.67s):** Prompt document glow intensifies. Category labels appear: "ARTIFACT" and "SOURCE OF TRUTH".
4. **Frame 80-100 (2.67-3.33s):** Directional arrows draw between the documents: "generates →" and "← extracts".
5. **Frame 100-120 (3.33-4s):** Bottom annotation text fades in. "source of truth" highlights in purple.
6. **Frame 120-150 (4-5s):** Hold. Prompt pulses gently. Full contrast visible.

### Typography
- File labels: JetBrains Mono (code), Inter (prompt), 12px
- Code body: JetBrains Mono, 11px, `#475569` at 0.4
- Prompt body: Inter, 12px, `#E2E8F0` at 0.8
- "ARTIFACT" watermark: Inter, 36px, bold (700), `#475569` at 0.15
- Category labels: Inter, 16px, semi-bold (600)
- Directional labels: Inter, 13px
- Bottom annotation: Inter, 18px, `#E2E8F0` at 0.7

### Easing
- Document slide-in: `easeOut(cubic)` over 20 frames, 30px distance
- Watermark stamp: `easeOut(back)` over 15 frames (slight bounce)
- Glow intensify: `easeOut(quad)` over 20 frames
- Arrow draw: `easeInOut(quad)` over 15 frames
- Bottom text fade-in: `easeOut(quad)` over 20 frames
- Prompt pulse: `easeInOut(sine)` on 45-frame cycle

## Narration Sync
> "When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001` (closing beats)

- **0:12** (12.00s): Documents appear side by side — "regenerated version passes all tests"
- **0:14** (14.00s): Category labels — "the prompt is your new source of truth"
- **0:15** (15.12s): Hold — segment ends, transition

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Code document — artifact */}
    <Sequence from={0}>
      <SlideIn from="left" distance={30} duration={20}>
        <FadeIn duration={20}>
          <DocumentCard
            x={340} y={300} width={380} height={260}
            fill="#1E1E2E" borderColor="#475569" borderStyle="dashed"
            label="auth_handler.py" labelFont="JetBrains Mono"
            labelColor="#475569"
          >
            <CodeLines lines={6} font="JetBrains Mono" size={11}
              color="#475569" opacity={0.4} />
          </DocumentCard>
        </FadeIn>
      </SlideIn>
    </Sequence>

    {/* ARTIFACT watermark */}
    <Sequence from={20}>
      <StampIn duration={15} easing="easeOut(back)">
        <Text text="ARTIFACT" font="Inter" size={36} weight={700}
          color="#475569" opacity={0.15} rotation={-15}
          x={530} y={430} align="center" />
      </StampIn>
    </Sequence>

    {/* Prompt document — source of truth */}
    <Sequence from={0}>
      <SlideIn from="right" distance={30} duration={20}>
        <FadeIn duration={20}>
          <DocumentCard
            x={1200} y={300} width={380} height={260}
            fill="#1E1E2E" borderColor="#8B5CF6" borderStyle="solid"
            label="auth_handler.prompt.md" labelFont="Inter"
            labelColor="#8B5CF6"
            glow={{ color: "#8B5CF6", opacity: 0.1, radius: 16 }}
            pulseCycle={45}
          >
            <SpecLines lines={5} font="Inter" size={12}
              color="#E2E8F0" opacity={0.8} />
          </DocumentCard>
        </FadeIn>
      </SlideIn>
    </Sequence>

    {/* Category labels */}
    <Sequence from={50}>
      <FadeIn duration={15}>
        <Text text="ARTIFACT" font="Inter" size={16} weight={600}
          color="#475569" opacity={0.6} x={530} y={590} align="center" />
        <Text text="SOURCE OF TRUTH" font="Inter" size={16} weight={600}
          color="#8B5CF6" opacity={0.8} x={1390} y={590} align="center" />
      </FadeIn>
    </Sequence>

    {/* Directional labels */}
    <Sequence from={80}>
      <DrawArrow label="generates →" color="#4A90D9" opacity={0.5}
        from={{ x: 1000, y: 410 }} to={{ x: 800, y: 410 }}
        font="Inter" fontSize={13} drawDuration={15} />
      <DrawArrow label="← extracts" color="#64748B" opacity={0.4}
        from={{ x: 800, y: 440 }} to={{ x: 1000, y: 440 }}
        font="Inter" fontSize={13} drawDuration={15} />
    </Sequence>

    {/* Bottom annotation */}
    <Sequence from={100}>
      <FadeIn duration={20}>
        <RichText x={960} y={750} align="center" font="Inter" size={18}>
          <Span color="#E2E8F0" opacity={0.7}>
            When the regenerated version passes all tests, the prompt is your new{' '}
          </Span>
          <Span color="#8B5CF6" opacity={0.9} weight={600}>
            source of truth
          </Span>
          <Span color="#E2E8F0" opacity={0.7}>.</Span>
        </RichText>
      </FadeIn>
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "comparison_diagram",
  "left": {
    "label": "auth_handler.py",
    "category": "ARTIFACT",
    "borderStyle": "dashed",
    "borderColor": "#475569",
    "watermark": "ARTIFACT"
  },
  "right": {
    "label": "auth_handler.prompt.md",
    "category": "SOURCE OF TRUTH",
    "borderStyle": "solid",
    "borderColor": "#8B5CF6",
    "glow": true
  },
  "relationships": [
    { "direction": "right_to_left", "label": "generates →" },
    { "direction": "left_to_right", "label": "← extracts" }
  ],
  "annotation": "When the regenerated version passes all tests, the prompt is your new source of truth.",
  "narrationSegments": ["where_to_start_001"]
}
```

---
