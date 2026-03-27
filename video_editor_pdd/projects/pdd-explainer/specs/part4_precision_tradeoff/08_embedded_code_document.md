[Remotion]

# Section 4.8: Embedded Code in Prompt Document

**Tool:** Remotion
**Duration:** ~28s (840 frames @ 30fps)
**Timestamp:** 1:04 - 1:32

## Visual Description

A prompt document displayed as a stylized manuscript page, with a code block visually embedded inside it. This shows the boundary between natural language and code within a PDD prompt — and how that boundary is fluid, not binary.

**The Document:** A large prompt file rendered as a flowing document. The natural language portions have a soft, warm appearance — rounded edges, serif-like rendering hints, flowing line lengths. The text describes architecture, intent, constraints in natural language.

**The Embedded Code Block:** Mid-document, a distinct code block appears — sharp rectangular edges, monospace font, slightly recessed background (`#111827`), with a thin left border accent (`#64748B`). This block contains a specific algorithm implementation (e.g., a sorting comparator or a hash function). It's visually "harder" and more rigid than the surrounding prose.

**The Label:** Below the document: "The boundary between prompt and code is fluid." This fades in after the code block is highlighted.

**The Concept:** The narration explains that most specification stays in natural language, but algorithm-critical sections can embed actual code. It's not all-or-nothing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Document Container
- Position: centered, 1000×720px
- Background: `#0F172A` at 0.8, 1px border `#1E293B`, rounded 12px
- Inner padding: 48px
- Subtle paper texture: very faint diagonal lines, `#1E293B` at 0.02

#### Natural Language Sections
- Font: Inter, 15px, regular (400), `#CBD5E1` at 0.85
- Line height: 1.6
- Paragraph spacing: 20px
- Text has slight warm tint — `#D4C5B0` at 0.1 overlay
- Content (representative):
  - "## Parser Module" (heading)
  - "Parse incoming JSON payloads according to schema..."
  - "Handle malformed input by returning structured errors..."
  - "Support nested objects up to 5 levels deep..."
  - [code block appears here]
  - "For all other formatting, follow standard conventions..."

#### Embedded Code Block
- Position: inset from document margins, full-width within container
- Background: `#111827`, 1px border `#334155`, rounded 6px
- Left accent border: 3px, `#64748B`
- Font: JetBrains Mono, 13px, regular (400), `#A5F3FC` (cyan tint for code)
- Content: ~8 lines of algorithm code (comparison function)
- Highlight glow: `#4A90D9` at 0.08, 8px blur (activates on focus)

#### Annotations
- Arrow from natural language with label "Natural language" — `#D9944A` at 0.5
- Arrow from code block with label "Embedded code" — `#4A90D9` at 0.5
- Bottom label: "The boundary between prompt and code is fluid." — Inter, 18px, `#94A3B8`

### Animation Sequence
1. **Frame 0-60 (0-2s):** Document container fades in. Natural language text begins revealing top-down, flowing like it's being written.
2. **Frame 60-180 (2-6s):** Text continues revealing. The prose sections fill in — architecture, intent, constraints. Warm, flowing, readable.
3. **Frame 180-300 (6-10s):** The embedded code block appears — sharp edges, monospace, distinct background. It's visually jarring against the prose. The contrast is deliberate. Code block glow activates.
4. **Frame 300-420 (10-14s):** Remaining natural language appears below the code block. The document is complete. Two annotation arrows appear — one from prose ("Natural language"), one from code block ("Embedded code").
5. **Frame 420-540 (14-18s):** Bottom label appears: "The boundary between prompt and code is fluid." Hold.
6. **Frame 540-780 (18-26s):** Hold across remaining narration about dipping into code when precision demands it.
7. **Frame 780-840 (26-28s):** Fade out.

### Typography
- Document heading: Inter, 20px, bold (700), `#E2E8F0`
- Prose text: Inter, 15px, regular (400), `#CBD5E1` at 0.85
- Code text: JetBrains Mono, 13px, regular (400), `#A5F3FC`
- Annotation labels: Inter, 13px, regular (400), respective colors at 0.5
- Bottom label: Inter, 18px, regular (400), `#94A3B8`

### Easing
- Document fade-in: `easeOut(quad)` over 30 frames
- Text reveal: `linear` scroll, 1 line per 8 frames
- Code block appear: `easeOut(cubic)` with scale 0.98→1.0 over 20 frames
- Code glow: `easeOut(quad)` over 15 frames
- Annotation arrows: `easeOut(quad)` draw over 20 frames each
- Bottom label: `easeOut(quad)` fade over 20 frames
- Fade out: `easeIn(quad)` over 60 frames

## Narration Sync
> "But some things genuinely need code-level precision. Algorithm choice. Performance-critical inner loops. Bit-level operations."
> "PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all-or-nothing. You stay in prompt space for as long as possible — architecture, intent, constraints, edge cases — then dip into code when the precision demands it."

Segments: `part4_precision_tradeoff_004`

- **64.64s** (seg 004): Document begins — "But some things genuinely need code-level precision"
- **70.00s**: Prose sections visible — "Algorithm choice. Performance-critical inner loops"
- **76.00s**: Code block appears — "PDD handles this. A prompt can embed code snippets"
- **82.00s**: Annotations visible — "It's not all-or-nothing"
- **86.00s**: Bottom label — "stay in prompt space for as long as possible"
- **92.54s** (seg 004 ends): Hold, begin fade

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={840}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Document container */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <DocumentContainer
          position={{ x: 460, y: 140 }}
          width={1000} height={720}
          bgColor="#0F172A" borderColor="#1E293B"
          cornerRadius={12} padding={48}
        >
          {/* Prose sections - above code */}
          <Sequence from={30}>
            <TextReveal rate={8}>
              <Heading text="## Parser Module"
                font="Inter" size={20} color="#E2E8F0" />
              <Paragraph text={proseAboveCode}
                font="Inter" size={15} color="#CBD5E1"
                lineHeight={1.6} />
            </TextReveal>
          </Sequence>

          {/* Embedded code block */}
          <Sequence from={180}>
            <ScaleIn from={0.98} duration={20}>
              <CodeEmbed
                bgColor="#111827" borderColor="#334155"
                accentBorder={{ width: 3, color: "#64748B" }}
                cornerRadius={6}
                glowColor="#4A90D9" glowOpacity={0.08}
              >
                <Code text={embeddedAlgorithm}
                  font="JetBrains Mono" size={13}
                  color="#A5F3FC" />
              </CodeEmbed>
            </ScaleIn>
          </Sequence>

          {/* Prose sections - below code */}
          <Sequence from={300}>
            <TextReveal rate={8}>
              <Paragraph text={proseBelowCode}
                font="Inter" size={15} color="#CBD5E1" />
            </TextReveal>
          </Sequence>
        </DocumentContainer>
      </FadeIn>
    </Sequence>

    {/* Annotation arrows */}
    <Sequence from={300}>
      <AnnotationArrow
        from={{ x: 380, y: 350 }} to={{ x: 460, y: 350 }}
        label="Natural language" color="#D9944A" opacity={0.5} />
      <AnnotationArrow
        from={{ x: 380, y: 550 }} to={{ x: 460, y: 550 }}
        label="Embedded code" color="#4A90D9" opacity={0.5} />
    </Sequence>

    {/* Bottom label */}
    <Sequence from={420}>
      <FadeIn duration={20}>
        <Text text="The boundary between prompt and code is fluid."
          font="Inter" size={18} color="#94A3B8"
          x={960} y={920} align="center" />
      </FadeIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={780}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "document_visualization",
  "chartId": "embedded_code_document",
  "document": {
    "title": "Parser Module",
    "sections": [
      { "type": "prose", "content": "Parse incoming JSON payloads according to schema...", "lines": 8 },
      { "type": "prose", "content": "Handle malformed input by returning structured errors...", "lines": 6 },
      { "type": "code_embed", "content": "comparison_function", "lines": 8, "language": "python" },
      { "type": "prose", "content": "For all other formatting, follow standard conventions...", "lines": 4 }
    ]
  },
  "annotations": [
    { "target": "prose", "label": "Natural language", "color": "#D9944A" },
    { "target": "code_embed", "label": "Embedded code", "color": "#4A90D9" }
  ],
  "label": "The boundary between prompt and code is fluid.",
  "narrationSegments": ["part4_precision_tradeoff_004"]
}
```

---
