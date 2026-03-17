[Remotion]

# Section 4.8: Embedded Code Document — Prompt with Code Islands

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 19:46 - 20:00

## Visual Description

A prompt document fills the center of the screen, rendered as a stylized code editor pane. The document is mostly flowing natural language (soft, rounded text in blue-tinted white) with three distinct "code islands" embedded within it — blocks of sharp-edged, monospace code that stand out visually from the surrounding prose.

The natural language sections flow like a river of text, describing architecture and intent. The code blocks are visually distinct — they have crisp borders, darker backgrounds, and monospace font. They represent the moments where precision demands code-level specificity: an algorithm choice, a performance-critical inner loop, a bit-level operation.

A floating label reads: "The boundary between prompt and code is fluid." This label sits above the document and pulses gently.

The animation reveals the document top-to-bottom, with natural language flowing in smoothly and code blocks snapping in with a sharp, crystalline animation — visually distinguishing the two modes of specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (near-black navy)
- Subtle paper texture: noise at 0.02 opacity

### Chart/Visual Elements

#### Document Container
- Centered at (960, 500), 700x750px
- Background: `#0F172A` at 0.8
- Border: 1px, `#1E293B` at 0.3, rounded corners 8px
- Shadow: 0 4px 20px `#000000` at 0.3

#### File Header
- Tab: `module_spec.prompt` — JetBrains Mono, 11px, `#4A90D9` at 0.5
- Thin underline: `#4A90D9` at 0.2

#### Natural Language Sections (3 blocks)
- Font: Inter, 12px, `#CBD5E1` at 0.6
- Line height: 20px
- Left margin: 30px, right margin: 30px
- Text has soft, slightly rounded rendering feel
- Section 1 (top): ~6 lines about module architecture
  - "This module handles JSON parsing for the API gateway."
  - "It should support streaming input and produce an AST"
  - "that downstream validators can traverse depth-first."
  - "Error messages must include line and column numbers."
  - "Prioritize clarity of error messages over parse speed."
  - "The module will be regenerated frequently."
- Section 2 (middle): ~4 lines about error handling intent
  - "When encountering malformed input, the parser should"
  - "attempt recovery where possible, collecting multiple"
  - "errors rather than failing on the first. Report all"
  - "errors in a structured diagnostic format."
- Section 3 (bottom): ~3 lines about output format
  - "Output the AST as a typed Python dataclass hierarchy."
  - "Each node should carry source position metadata."
  - "Use Union types for polymorphic node variants."

#### Code Islands (3 blocks, visually distinct)
- Font: JetBrains Mono, 10px, `#E2E8F0` at 0.7
- Background: `#1E293B` at 0.6
- Border: 1px, `#334155` at 0.5, sharp corners (0px radius — deliberately angular)
- Left border accent: 3px, `#64748B` at 0.4
- Padding: 12px
- Each code block has a small label in top-right: "code" — JetBrains Mono, 7px, `#64748B` at 0.3

- **Code Island 1** (after section 1): Algorithm choice — 4 lines
  ```
  # Use recursive descent — NOT packrat.
  # Packrat's memory overhead is unacceptable
  # for streaming inputs > 100MB.
  def parse(tokens: Iterator[Token]) -> AST:
  ```

- **Code Island 2** (after section 2): Performance-critical loop — 3 lines
  ```
  # Hot loop — must process > 1M tokens/sec
  while token := next(tokens, None):
      node = DISPATCH_TABLE[token.type](token)
  ```

- **Code Island 3** (after section 3): Bit-level operation — 3 lines
  ```
  # Unicode surrogate pair decoding
  high = (codepoint - 0xD800) << 10
  char = chr(high + (low - 0xDC00) + 0x10000)
  ```

#### Floating Label
- "The boundary between prompt and code is fluid." — Inter, 16px, semi-bold (600), `#E2E8F0` at 0.6
- Position: centered at y: 80
- Subtle glow: `#E2E8F0` at 0.08, 10px blur
- Pulse: opacity oscillates 0.5 to 0.7

#### Visual Flow Lines
- Thin curved lines connecting natural language sections, flowing around code blocks
- `#4A90D9` at 0.06, 1px, dashed
- Suggest the river of prose that flows around the hard code islands

### Animation Sequence
1. **Frame 0-30 (0-1s):** Document container fades in. File header appears.
2. **Frame 30-80 (1-2.67s):** Natural language section 1 types in line-by-line, flowing and smooth. Text appears with a soft fade.
3. **Frame 80-110 (2.67-3.67s):** Code Island 1 snaps in — sharp crystalline animation. The block appears with a brief bright-edge flash (`#E2E8F0` at 0.3 on border for 5 frames). The visual contrast with the prose is stark.
4. **Frame 110-160 (3.67-5.33s):** Natural language section 2 flows in. Flow lines begin drawing around Code Island 1.
5. **Frame 160-190 (5.33-6.33s):** Code Island 2 snaps in with the same crystalline flash. "code" label appears.
6. **Frame 190-240 (6.33-8s):** Natural language section 3 flows in. More flow lines draw.
7. **Frame 240-270 (8-9s):** Code Island 3 snaps in. All three code blocks now visible, floating in the river of prose.
8. **Frame 270-330 (9-11s):** Floating label appears above: "The boundary between prompt and code is fluid." Pulses gently.
9. **Frame 330-380 (11-12.67s):** A subtle color wash highlights the ratio — natural language sections glow faintly blue, code blocks glow faintly gray. The document is ~80% blue, ~20% gray.
10. **Frame 380-420 (12.67-14s):** Hold. Label pulses. The hybrid document breathes.

### Typography
- File header: JetBrains Mono, 11px, `#4A90D9` at 0.5
- Natural language: Inter, 12px, `#CBD5E1` at 0.6
- Code blocks: JetBrains Mono, 10px, `#E2E8F0` at 0.7
- Code label: JetBrains Mono, 7px, `#64748B` at 0.3
- Floating label: Inter, 16px, semi-bold (600), `#E2E8F0` at 0.6

### Easing
- Container fade: `easeOut(quad)` over 20 frames
- Text flow: `easeOut(quad)` per line, 8 frames
- Code snap-in: `easeOut(back(2))` scale from 0.9 to 1.0, 12 frames
- Border flash: `easeOut(expo)` over 5 frames
- Flow lines draw: `easeInOut(cubic)` over 40 frames
- Label pulse: `easeInOut(sine)` on 50-frame cycle
- Color wash: `easeOut(quad)` over 30 frames

## Narration Sync
> "But some things genuinely need code-level precision. Algorithm choice. Performance-critical inner loops. Bit-level operations."
> "PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all-or-nothing. You stay in prompt space for as long as possible — architecture, intent, constraints, edge cases — then dip into code when the precision demands it."

Segment: `part4_008`

- **19:46** ("some things genuinely need code-level precision"): Document appearing, first prose section
- **19:50** ("Algorithm choice"): Code Island 1 snaps in — recursive descent comment
- **19:52** ("Performance-critical inner loops"): Code Island 2 snaps in — hot loop
- **19:54** ("Bit-level operations"): Code Island 3 snaps in — unicode decoding
- **19:56** ("A prompt can embed code snippets"): All code islands visible in prose river
- **20:00** ("then dip into code when the precision demands it"): Floating label visible, color wash showing ratio

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Document container */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <DocumentPane center={[960, 500]} size={[700, 750]}
          bgColor="#0F172A" borderColor="#1E293B"
          cornerRadius={8} shadow={true}>

          <FileTab name="module_spec.prompt" color="#4A90D9" />

          {/* Prose Section 1 */}
          <Sequence from={30}>
            <ProseBlock lines={proseSection1}
              font="Inter" size={12} color="#CBD5E1"
              lineHeight={20} fadePerLine={8} />
          </Sequence>

          {/* Code Island 1 — Algorithm choice */}
          <Sequence from={80}>
            <CodeIsland code={algorithmCode}
              font="JetBrains Mono" size={10}
              bgColor="#1E293B" borderColor="#334155"
              accentColor="#64748B" accentWidth={3}
              snapDuration={12} flashDuration={5} />
          </Sequence>

          {/* Prose Section 2 */}
          <Sequence from={110}>
            <ProseBlock lines={proseSection2}
              font="Inter" size={12} color="#CBD5E1"
              lineHeight={20} fadePerLine={8} />
          </Sequence>

          {/* Code Island 2 — Hot loop */}
          <Sequence from={160}>
            <CodeIsland code={hotLoopCode}
              snapDuration={12} flashDuration={5} />
          </Sequence>

          {/* Prose Section 3 */}
          <Sequence from={190}>
            <ProseBlock lines={proseSection3}
              font="Inter" size={12} color="#CBD5E1"
              lineHeight={20} fadePerLine={8} />
          </Sequence>

          {/* Code Island 3 — Bit-level */}
          <Sequence from={240}>
            <CodeIsland code={unicodeCode}
              snapDuration={12} flashDuration={5} />
          </Sequence>
        </DocumentPane>
      </FadeIn>
    </Sequence>

    {/* Flow lines around code blocks */}
    <Sequence from={110}>
      <FlowLines around={codeIslandPositions}
        color="#4A90D9" opacity={0.06}
        drawDuration={40} dashed={true} />
    </Sequence>

    {/* Floating label */}
    <Sequence from={270}>
      <PulsingLabel
        text="The boundary between prompt and code is fluid."
        font="Inter" size={16} weight={600}
        color="#E2E8F0" opacity={0.6}
        glow={{ radius: 10, opacity: 0.08 }}
        pulsePeriod={50} pulseRange={[0.5, 0.7]}
        x={960} y={80} align="center" />
    </Sequence>

    {/* Color wash — prose blue, code gray */}
    <Sequence from={330}>
      <ColorWash
        proseRegions={prosePositions} proseColor="#4A90D9" proseOpacity={0.04}
        codeRegions={codePositions} codeColor="#94A3B8" codeOpacity={0.04}
        fadeDuration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_document",
  "documentId": "embedded_code_document",
  "fileName": "module_spec.prompt",
  "sections": [
    { "type": "prose", "lineCount": 6, "topic": "Module architecture and intent" },
    { "type": "code", "lineCount": 4, "topic": "Algorithm choice (recursive descent)", "reason": "Memory constraints for streaming" },
    { "type": "prose", "lineCount": 4, "topic": "Error handling philosophy" },
    { "type": "code", "lineCount": 3, "topic": "Performance-critical hot loop", "reason": "Must process > 1M tokens/sec" },
    { "type": "prose", "lineCount": 3, "topic": "Output format specification" },
    { "type": "code", "lineCount": 3, "topic": "Bit-level unicode operation", "reason": "Surrogate pair decoding" }
  ],
  "ratio": { "prose": 0.8, "code": 0.2 },
  "floatingLabel": "The boundary between prompt and code is fluid.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_008"]
}
```

---
