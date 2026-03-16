[Remotion]

# Section 4.6: Embedded Code Document — The Fluid Boundary

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 1:04 – 1:22

## Visual Description
A single prompt document occupies center-screen, showing a real-world PDD prompt that contains both natural language sections and an embedded code block. The natural language regions (architecture, intent, constraints) are highlighted in blue, flowing and organic. The embedded code block (a performance-critical algorithm) is highlighted with sharp monospace styling and a distinct border. Arrows or region labels identify which parts are "prompt space" and which are "code space." Three category callouts appear sequentially — "Algorithm choice", "Performance-critical inner loops", "Bit-level operations" — each with a brief code snippet example. The visual establishes that PDD prompts can embed code when precision demands it.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- No grid lines

### Chart/Visual Elements
- **Prompt document:** 700×600px, centered at (960, 420), dark bg `#1A2332`, border `#4A90D9` at 0.15 opacity, 1px, rounded 8px
  - **Natural language regions (3 blocks):**
    - Block 1 (y: 140–220): "# Architecture\nImplement a streaming parser that reads JSON and YAML inputs.\nReturn an AST with typed nodes." — blue left-border accent (3px, `#4A90D9`)
    - Block 2 (y: 230–290): "# Constraints\n- Handle null/empty inputs gracefully\n- Support nested structures up to depth 10" — blue left-border accent
    - Block 3 (y: 440–520): "# Edge Cases\n- Circular references: raise ParseError\n- Unicode: full UTF-8 support" — blue left-border accent
  - **Embedded code block (y: 300–430):**
    - Header: "```python  # critical: custom tokenizer" — `#94A3B8`, 11px
    - Code: 6 lines of Python (tokenizer inner loop), JetBrains Mono 12px, syntax-highlighted
    - Sharp border: 1px, `#D9944A` at 0.3 opacity (distinct from prompt sections)
    - Background: `#0D1117` (darker than prompt bg)
  - Region labels (outside document):
    - "Prompt space" arrow pointing to natural language blocks — `#4A90D9`, 14px
    - "Code space" arrow pointing to embedded code — `#D9944A`, 14px

- **Category callouts (right side, x: 1400–1800):**
  - Callout 1: "Algorithm choice" — icon: branching tree, `#D9944A`
    - Snippet: `heapq` vs `sorted()` — JetBrains Mono, 11px
  - Callout 2: "Performance-critical loops" — icon: lightning bolt, `#D9944A`
    - Snippet: `for i in range(n): ...` — JetBrains Mono, 11px
  - Callout 3: "Bit-level operations" — icon: binary `01`, `#D9944A`
    - Snippet: `flags & 0xFF` — JetBrains Mono, 11px
  - Each callout: 300×80px card, bg `#1A2332`, border `#D9944A` at 0.15 opacity

- **Boundary label:** "The boundary between prompt and code is fluid." — centered at (960, 840), `#FFFFFF` at 0.5 opacity, 18px

### Animation Sequence
1. **Frame 0–40 (0–1.33s):** Prompt document container fades in. Natural language Block 1 types on line-by-line with blue accent bar drawing downward.
2. **Frame 40–100 (1.33–3.33s):** Block 2 types on. Then the embedded code block appears — its darker background slides in, the code syntax-highlights character-by-character. The amber border around the code block draws in, visually distinct from the blue prompt sections.
3. **Frame 100–160 (3.33–5.33s):** Block 3 types on below the code. The document is now fully visible. Region labels ("Prompt space" and "Code space") fade in with thin connector arrows.
4. **Frame 160–260 (5.33–8.67s):** Category callouts appear sequentially on the right side, 30-frame stagger:
   - Callout 1: "Algorithm choice" slides in from right with snippet
   - Callout 2: "Performance-critical loops" slides in
   - Callout 3: "Bit-level operations" slides in
5. **Frame 260–360 (8.67–12.0s):** Each callout briefly highlights — a thin amber line connects it to the embedded code region of the prompt document, then fades to 0.2 opacity. Shows these are the exceptions that warrant code embedding.
6. **Frame 360–440 (12.0–14.67s):** Connector lines from callouts fade. The code block within the prompt pulses once with amber glow. The natural language blocks pulse once with blue glow. The fluid boundary is visually emphasized.
7. **Frame 440–500 (14.67–16.67s):** Boundary label types on at bottom: "The boundary between prompt and code is fluid."
8. **Frame 500–540 (16.67–18.0s):** Hold. Subtle ambient breathing on both colored regions.

### Typography
- Prompt natural language: Inter Regular, 14px, `#FFFFFF` at 0.6 opacity
- Prompt headings (#): Inter SemiBold, 15px, `#FFFFFF` at 0.8 opacity
- Embedded code: JetBrains Mono, 12px, syntax-highlighted (keywords `#79C0FF`, strings `#A5D6FF`, functions `#D2A8FF`)
- Code header: JetBrains Mono, 11px, `#94A3B8`
- Region labels: Inter Medium, 14px, respective colors
- Category callout title: Inter SemiBold, 14px, `#D9944A`
- Category snippet: JetBrains Mono, 11px, `#C9D1D9`
- Boundary label: Inter Regular, 18px, `#FFFFFF` at 0.5 opacity

### Easing
- Document fade: `easeOutCubic`
- Text type-on: linear (40ms/char)
- Code block slide: `easeOutQuad`
- Region label fade: `easeOutQuad`
- Callout slide-in: `spring({ damping: 15, stiffness: 100 })`
- Connector line draw: `easeOutCubic`
- Glow pulse: `easeInOutSine`
- Boundary label type-on: linear

## Narration Sync
> "But some things genuinely need code-level precision. Algorithm choice. Performance-critical inner loops. Bit-level operations."

> "PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all or nothing. You stay in prompt space for as long as possible. Architecture, intent, constraints, edge cases. Then dip into code when the precision demands it."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Prompt document container */}
    <Sequence from={0} durationInFrames={40}>
      <FadeIn>
        <PromptDocumentShell width={700} height={600} x={960} y={420} />
      </FadeIn>
    </Sequence>

    {/* Natural language Block 1 */}
    <Sequence from={0} durationInFrames={40}>
      <TypeOnBlock lines={architectureLines} accent="#4A90D9" />
    </Sequence>

    {/* Natural language Block 2 + Embedded code */}
    <Sequence from={40} durationInFrames={60}>
      <TypeOnBlock lines={constraintLines} accent="#4A90D9" />
      <EmbeddedCodeBlock code={tokenizerCode} border="#D9944A" bg="#0D1117" />
    </Sequence>

    {/* Natural language Block 3 + Region labels */}
    <Sequence from={100} durationInFrames={60}>
      <TypeOnBlock lines={edgeCaseLines} accent="#4A90D9" />
      <RegionLabels
        promptLabel="Prompt space"
        codeLabel="Code space"
        promptColor="#4A90D9"
        codeColor="#D9944A"
      />
    </Sequence>

    {/* Category callouts */}
    <Sequence from={160} durationInFrames={100}>
      <StaggeredCallouts
        callouts={categoryCallouts}
        stagger={30}
        slideDirection="right"
      />
    </Sequence>

    {/* Connector lines */}
    <Sequence from={260} durationInFrames={100}>
      <ConnectorLines from="callouts" to="code-block" color="#D9944A" />
    </Sequence>

    {/* Region glow pulses */}
    <Sequence from={360} durationInFrames={80}>
      <RegionGlow regions={["prompt", "code"]} colors={["#4A90D9", "#D9944A"]} />
    </Sequence>

    {/* Boundary label */}
    <Sequence from={440} durationInFrames={60}>
      <TypeOnText
        text="The boundary between prompt and code is fluid."
        y={840}
        color="#FFFFFF"
        opacity={0.5}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "promptDocument": {
    "width": 700,
    "height": 600,
    "naturalLanguageBlocks": [
      {
        "heading": "Architecture",
        "lines": [
          "Implement a streaming parser that reads JSON and YAML inputs.",
          "Return an AST with typed nodes."
        ]
      },
      {
        "heading": "Constraints",
        "lines": [
          "- Handle null/empty inputs gracefully",
          "- Support nested structures up to depth 10"
        ]
      },
      {
        "heading": "Edge Cases",
        "lines": [
          "- Circular references: raise ParseError",
          "- Unicode: full UTF-8 support"
        ]
      }
    ],
    "embeddedCode": {
      "language": "python",
      "header": "# critical: custom tokenizer",
      "lines": [
        "def tokenize(stream: IO) -> Iterator[Token]:",
        "    buf = stream.read(CHUNK_SIZE)",
        "    while buf:",
        "        for match in TOKEN_RE.finditer(buf):",
        "            yield Token(match.group(), match.start())",
        "        buf = stream.read(CHUNK_SIZE)"
      ]
    }
  },
  "categoryCallouts": [
    { "title": "Algorithm choice", "icon": "tree", "snippet": "heapq vs sorted()" },
    { "title": "Performance-critical loops", "icon": "lightning", "snippet": "for i in range(n): ..." },
    { "title": "Bit-level operations", "icon": "binary", "snippet": "flags & 0xFF" }
  ]
}
```

---
