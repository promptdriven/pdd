[Remotion]

# Section 4.6: Embedded Code Document — Prompt with Code Snippets

**Tool:** Remotion
**Duration:** ~31s (942 frames @ 30fps)
**Timestamp:** 1:05 - 1:36

## Visual Description

A richly animated visualization of a prompt document that contains an embedded code block — showing that the boundary between prompt and code is fluid, not binary.

The composition opens with a stylized prompt document floating center-screen. The document is rendered as a card with soft rounded corners, primarily filled with flowing natural-language text (rendered as readable paragraph blocks in a warm serif-like style). The text is clearly natural language — "The parser shall accept...", "Edge cases include...", "Error handling should...".

Then, partway down the document, a CODE BLOCK appears — visually distinct. It has sharp rectangular edges, monospace font, a slightly darker background, and syntax highlighting. It's embedded INSIDE the natural-language document. This is a code snippet handling a critical section — perhaps a regex pattern or a precise algorithm that natural language can't capture efficiently.

The visual emphasizes the contrast: flowing organic text surrounding a precise mechanical code block. A label appears: "The boundary between prompt and code is fluid."

Around the document, subtle annotations float in:
- Arrow pointing to natural language sections: "Architecture, intent, constraints"
- Arrow pointing to code block: "Precision where it matters"
- A dashed outline showing the code block could be smaller or larger — the boundary is adjustable.

The document holds for a long narration about staying in prompt space and dipping into code when precision demands it.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Prompt Document Card
- Dimensions: 720×700px, centered at (960, 480)
- Background: `#151B2B` (slightly lighter than canvas)
- Border: `#334155` at 0.3, rounded 12px
- Drop shadow: `#000000` at 0.2, 0 4px 20px

#### Natural Language Sections
- Font: Inter, 12px, `#C8D0E0` at 0.7, line-height 1.6
- Paragraph blocks with 20px padding
- Sections:
  - Top block (lines 1-8): "The parser shall accept JSON and YAML inputs. It must handle nested structures to a depth of 10..." — warm, flowing text
  - Middle block (lines 12-18): "Edge cases include: empty input, malformed brackets, Unicode escaping..." — slightly indented list
  - Bottom block (lines 24-30): "Error handling should surface line numbers and column positions..." — concluding requirements
- Visual style: text appears as soft, organic blocks with natural paragraph spacing

#### Embedded Code Block
- Position: between middle and bottom natural-language sections (lines 19-23)
- Dimensions: 660×120px, inset 30px from document edges
- Background: `#0D1117` (dark code editor bg)
- Border: `#2DD4BF` at 0.3, sharp corners (2px radius) — deliberately angular
- Font: JetBrains Mono, 11px, syntax-highlighted
  - Keywords: `#C678DD` (purple)
  - Strings: `#98C379` (green)
  - Functions: `#61AFEF` (blue)
  - Punctuation: `#ABB2BF` (light gray)
- Content: a 5-line regex/algorithm snippet, e.g.:
  ```
  def validate_token(token: str) -> bool:
      pattern = r'^[a-zA-Z_]\w{0,63}$'
      if not re.match(pattern, token):
          raise TokenError(f"Invalid: {token}", col=self.pos)
      return True
  ```
- Glow: `#2DD4BF` at 0.08, 4px radius on edges — subtle emphasis

#### Label
- "The boundary between prompt and code is fluid." — Inter, 18px, semi-bold (600), `#E2E8F0` at 0.8
- Position: centered below document at y: 870

#### Floating Annotations
- Left annotation: arrow from left pointing to natural-language sections
  - "Architecture, intent, constraints" — Inter, 12px, `#A78BFA` at 0.5
  - Arrow: `#A78BFA` at 0.3, 1.5px, with arrowhead
- Right annotation: arrow from right pointing to code block
  - "Precision where it matters" — Inter, 12px, `#2DD4BF` at 0.5
  - Arrow: `#2DD4BF` at 0.3, 1.5px, with arrowhead
- Dashed outline: surrounds code block, `#475569` at 0.2, dashed (4px dash, 4px gap)
  - Pulses slightly — implying the boundary can expand or contract

### Animation Sequence
1. **Frame 0-30 (0-1s):** Document card fades in from slight scale-up (0.95 → 1.0). Blueprint grid visible.
2. **Frame 30-120 (1-4s):** Natural-language text types in block by block — top section first. Warm, organic feel.
3. **Frame 120-210 (4-7s):** Middle natural-language section appears. Then the code block slides in — sharp edges, distinct background, syntax highlighting. Visual contrast is immediate.
4. **Frame 210-300 (7-10s):** Bottom natural-language section appears below code block. The document is complete — flowing text with a precise code island inside.
5. **Frame 300-420 (10-14s):** Label appears: "The boundary between prompt and code is fluid." Floating annotations slide in from left and right.
6. **Frame 420-540 (14-18s):** Dashed outline appears around code block. It pulses — the boundary breathes. The code block briefly expands (grows 2 more lines) then contracts (shrinks by 1 line) — showing fluidity.
7. **Frame 540-750 (18-25s):** Hold. Annotations and document stable. The composition breathes — code block glow pulses subtly.
8. **Frame 750-900 (25-30s):** Annotations rearrange. A new label appears: "Stay in prompt space. Dip into code when you must." — Inter, 14px, `#94A3B8` at 0.5.
9. **Frame 900-942 (30-31.4s):** Begin fade-out. Document scales down slightly (1.0 → 0.97) while fading.

### Typography
- Natural language: Inter, 12px, `#C8D0E0` at 0.7, line-height 1.6
- Code: JetBrains Mono, 11px, syntax-highlighted
- Label: Inter, 18px, semi-bold (600), `#E2E8F0` at 0.8
- Annotations: Inter, 12px, respective colors at 0.5
- Secondary label: Inter, 14px, `#94A3B8` at 0.5

### Easing
- Document card appear: `easeOut(cubic)` scale + fade over 30 frames
- Text type-in: `easeOut(quad)` per block, 30 frames
- Code block slide-in: `easeOut(back)` over 25 frames — slight overshoot for distinction
- Label appear: `easeOut(quad)` over 20 frames
- Annotation slide: `easeOut(cubic)` over 30 frames
- Dashed outline pulse: `easeInOut(sine)` on 90-frame cycle
- Code block expand/contract: `easeInOut(cubic)` over 40 frames each
- Code block glow pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 42 frames

## Narration Sync
> "But some things genuinely need code-level precision. A regex pattern. A specific algorithm. A performance-critical path."
> "PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all-or-nothing."
> "You stay in prompt space for as long as possible — architecture, intent, constraints, edge cases — then dip into code when the precision demands it."

Segments: `part4_precision_tradeoff_009`

- **64.58s** (seg 009): Document card appears
- **68s**: Natural language sections typing in
- **72s**: Code block slides in — visual contrast
- **78s**: Label appears, annotations slide in
- **85s**: Dashed outline pulses, boundary fluidity
- **90s**: "Stay in prompt space" label
- **95.98s** (seg 009 ends): Begin fade-out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={942}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Document card */}
    <Sequence from={0}>
      <ScaleIn from={0.95} to={1.0} duration={30}>
        <FadeIn duration={30}>
          <DocumentCard x={600} y={130} width={720} height={700}
            bg="#151B2B" border="#334155" borderOpacity={0.3}
            borderRadius={12} shadow="0 4px 20px rgba(0,0,0,0.2)">

            {/* Top natural language block */}
            <Sequence from={30}>
              <TypeBlock lines={8} font="Inter" size={12}
                color="#C8D0E0" opacity={0.7} lineHeight={1.6}
                text="The parser shall accept JSON and YAML inputs. It must handle nested structures to a depth of 10. Input validation occurs before parsing begins..."
                padding={20} typeDuration={40} />
            </Sequence>

            {/* Middle natural language block */}
            <Sequence from={120}>
              <TypeBlock lines={6} font="Inter" size={12}
                color="#C8D0E0" opacity={0.7} lineHeight={1.6}
                text="Edge cases include: empty input, malformed brackets, Unicode escaping, deeply nested arrays beyond depth limit..."
                padding={20} typeDuration={30} indent={10} />
            </Sequence>

            {/* Embedded code block */}
            <Sequence from={150}>
              <SlideIn direction="left" distance={20} duration={25}>
                <CodeBlock x={30} y={320} width={660} height={120}
                  bg="#0D1117" border="#2DD4BF" borderOpacity={0.3}
                  borderRadius={2} glowColor="#2DD4BF" glowOpacity={0.08}
                  font="JetBrains Mono" fontSize={11}
                  content={`def validate_token(token: str) -> bool:\n    pattern = r'^[a-zA-Z_]\\w{0,63}$'\n    if not re.match(pattern, token):\n        raise TokenError(f"Invalid: {token}", col=self.pos)\n    return True`}
                  syntaxHighlight={{
                    keywords: "#C678DD",
                    strings: "#98C379",
                    functions: "#61AFEF",
                    punctuation: "#ABB2BF"
                  }} />
              </SlideIn>
            </Sequence>

            {/* Bottom natural language block */}
            <Sequence from={210}>
              <TypeBlock lines={6} font="Inter" size={12}
                color="#C8D0E0" opacity={0.7} lineHeight={1.6}
                text="Error handling should surface line numbers and column positions. The error message format must be human-readable..."
                padding={20} typeDuration={30} />
            </Sequence>
          </DocumentCard>
        </FadeIn>
      </ScaleIn>
    </Sequence>

    {/* Main label */}
    <Sequence from={300}>
      <FadeIn duration={20}>
        <Text text="The boundary between prompt and code is fluid."
          font="Inter" size={18} weight={600} color="#E2E8F0" opacity={0.8}
          x={960} y={870} align="center" />
      </FadeIn>
    </Sequence>

    {/* Left annotation — natural language */}
    <Sequence from={330}>
      <SlideIn direction="left" distance={30} duration={30}>
        <AnnotationArrow from={[200, 350]} to={[580, 350]}
          color="#A78BFA" opacity={0.3} width={1.5} />
        <Text text="Architecture, intent, constraints"
          font="Inter" size={12} color="#A78BFA" opacity={0.5}
          x={180} y={330} align="right" />
      </SlideIn>
    </Sequence>

    {/* Right annotation — code block */}
    <Sequence from={360}>
      <SlideIn direction="right" distance={30} duration={30}>
        <AnnotationArrow from={[1760, 450]} to={[1340, 450]}
          color="#2DD4BF" opacity={0.3} width={1.5} />
        <Text text="Precision where it matters"
          font="Inter" size={12} color="#2DD4BF" opacity={0.5}
          x={1780} y={430} align="left" />
      </SlideIn>
    </Sequence>

    {/* Dashed outline around code block */}
    <Sequence from={420}>
      <PulsingDashedRect x={625} y={445} width={670} height={130}
        color="#475569" opacity={0.2} dashArray={[4, 4]}
        pulseScale={[1.0, 1.05]} pulseDuration={90} />
    </Sequence>

    {/* Secondary label */}
    <Sequence from={750}>
      <FadeIn duration={20}>
        <Text text="Stay in prompt space. Dip into code when you must."
          font="Inter" size={14} color="#94A3B8" opacity={0.5}
          x={960} y={920} align="center" />
      </FadeIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={900}>
      <ScaleOut from={1.0} to={0.97} duration={42}>
        <FadeOut duration={42} />
      </ScaleOut>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "document_visualization",
  "document": {
    "width": 720,
    "height": 700,
    "sections": [
      { "type": "natural_language", "lines": 8, "topic": "parser_requirements" },
      { "type": "natural_language", "lines": 6, "topic": "edge_cases" },
      { "type": "code_block", "lines": 5, "language": "python", "topic": "token_validation" },
      { "type": "natural_language", "lines": 6, "topic": "error_handling" }
    ]
  },
  "annotations": [
    { "target": "natural_language", "label": "Architecture, intent, constraints", "color": "#A78BFA" },
    { "target": "code_block", "label": "Precision where it matters", "color": "#2DD4BF" }
  ],
  "labels": [
    "The boundary between prompt and code is fluid.",
    "Stay in prompt space. Dip into code when you must."
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_009"]
}
```

---
