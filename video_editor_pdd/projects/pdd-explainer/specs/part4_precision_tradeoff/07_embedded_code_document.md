[Remotion]

# Section 4.7: Embedded Code Document — The Fluid Boundary Between Prompt and Code

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 19:39 - 19:55

## Visual Description

A single prompt document is shown at large scale, filling most of the frame. The document is a `.prompt` file rendered in an editor-like view. Most of the content is natural language (flowing, blue-tinted text), but embedded within it is a code block — visually distinct with a sharp-edged background, monospace font, and gray tint.

The document structure:
- **Lines 1-8:** Natural language — intent, architecture, constraints. Flowing text in blue-white.
- **Lines 9-18:** An embedded code block (fenced with triple backticks). Sharp monospace font. Gray background. This is an algorithm implementation — a performance-critical inner loop that needs code-level precision.
- **Lines 19-24:** Back to natural language — edge case handling, return types.

The boundary between natural language and code is literally visible as a material transition. The natural language sections have a soft, flowing quality (subtle blue ambient glow). The code block has hard edges, grid-like alignment, and a cooler gray tone.

A floating annotation appears: "Stay in prompt space as long as possible. Dip into code when you must." Three inline labels highlight the sections: "Intent (natural language)", "Critical algorithm (code)", "Constraints (natural language)."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Document Frame
- Editor window: 1200×800px, centered at (960, 480)
- Window chrome: 30px title bar, `#1E293B`, rounded top corners 8px
- Title bar text: `ad_latency_optimizer.prompt` — JetBrains Mono, 11px, `#4A90D9` at 0.7
- Editor background: `#0F172A`
- Line numbers: JetBrains Mono, 10px, `#64748B` at 0.25, 40px left gutter

#### Natural Language Sections (lines 1-8, 19-24)
- Font: Inter, 13px, `#CBD5E1` at 0.8
- Ambient glow: `#4A90D9` at 0.03, 20px blur on text lines
- Line content examples:
  - Line 1: `# Ad Latency Optimizer`
  - Line 2: `Optimize bid calculation to meet sub-millisecond target.`
  - Line 3: `Accept bid request with up to 50 ad candidates.`
  - Line 4: `Score each candidate using CTR model output.`
  - Line 5: `Return top-k candidates sorted by expected value.`
  - Lines 6-8: constraint descriptions

#### Embedded Code Block (lines 9-18)
- Background: `#1A1F2E` — distinct from surrounding editor background
- Left border: 3px solid `#94A3B8` at 0.3
- Font: JetBrains Mono, 11px, `#94A3B8` at 0.7
- Code content: a sorting/scoring inner loop in Python
  - Line 9: ` ```python`
  - Line 10: `def score_candidates(candidates, ctr_scores):`
  - Line 11: `    # Vectorized scoring — numpy required for latency`
  - Line 12: `    scores = np.multiply(ctr_scores, candidates.bids)`
  - Line 13: `    top_k_idx = np.argpartition(scores, -k)[-k:]`
  - Line 14: `    return candidates[top_k_idx[np.argsort(scores[top_k_idx])[::-1]]]`
  - Lines 15-17: additional implementation detail
  - Line 18: ` ```  `
- No ambient glow — sharp, precise, mechanical

#### Section Labels (floating, right side of document)
- "Intent (natural language)" — Inter, 11px, `#4A90D9` at 0.5, bracket spanning lines 1-8
- "Critical algorithm (code)" — Inter, 11px, `#94A3B8` at 0.5, bracket spanning lines 9-18
- "Constraints (natural language)" — Inter, 11px, `#4A90D9` at 0.5, bracket spanning lines 19-24

#### Floating Annotation (below document, y: 920)
- "Stay in prompt space as long as possible. Dip into code when you must." — Inter, 14px, `#E2E8F0` at 0.6
- "prompt space" in `#4A90D9`, "code" in `#94A3B8`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Editor window frame appears. Title bar with filename. Empty editor.
2. **Frame 30-120 (1-4s):** Natural language lines 1-8 type in smoothly. Blue ambient glow appears around each line as it completes. Section label "Intent" draws its bracket.
3. **Frame 120-140 (4-4.67s):** Brief pause. The code block background rectangle slides in — a visual material change. Left border draws.
4. **Frame 140-240 (4.67-8s):** Code lines 9-18 type in with monospace cadence. No glow — stark, precise. The visual contrast with the natural language above is immediate. Section label "Critical algorithm" draws.
5. **Frame 240-260 (8-8.67s):** Code block closes. Another material transition back to natural language.
6. **Frame 260-340 (8.67-11.3s):** Natural language lines 19-24 type in. Blue glow returns. Section label "Constraints" draws. The full document is visible.
7. **Frame 340-420 (11.3-14s):** Labels pulse gently to emphasize the three regions. The boundary between prompt and code is clearly visible.
8. **Frame 420-480 (14-16s):** Floating annotation fades in below document. Hold.

### Typography
- Window title: JetBrains Mono, 11px, `#4A90D9` at 0.7
- Natural language: Inter, 13px, `#CBD5E1` at 0.8
- Code: JetBrains Mono, 11px, `#94A3B8` at 0.7
- Section labels: Inter, 11px, respective colors at 0.5
- Annotation: Inter, 14px, `#E2E8F0` at 0.6

### Easing
- Window appear: `easeOut(cubic)` over 20 frames
- Line typing: `linear`, 2 characters per frame
- Code block bg slide: `easeOut(cubic)` over 15 frames
- Label bracket draw: `easeOut(quad)` over 20 frames
- Label pulse: `easeInOut(sine)` single cycle
- Annotation fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "But some things genuinely need code-level precision. Algorithm choice. Performance-critical inner loops. Bit-level operations."
> "PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all-or-nothing."
> "You stay in prompt space for as long as possible — architecture, intent, constraints, edge cases — then dip into code when the precision demands it."

Segment: `part4_precision_tradeoff_009`

- **64.58s** ("But some things genuinely need code-level precision"): Editor window appears, natural language begins typing
- **68.14s** ("Algorithm choice"): Lines about scoring/optimization visible
- **69.62s** ("Performance-critical inner loops"): Code block background slides in
- **74.68s** ("PDD handles this"): Code block visible — the embedded algorithm
- **76.56s** ("A prompt can embed code snippets"): Full code block typed, section labels appearing
- **81.46s** ("It's not all-or-nothing"): All three sections labeled
- **83.58s** ("You stay in prompt space for as long as possible"): Natural language sections highlighted
- **93.14s** ("dip into code when the precision demands it"): Code section highlighted, annotation visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Editor window */}
    <Sequence from={0}>
      <EditorWindow
        position={[360, 80]} size={[1200, 800]}
        filename="ad_latency_optimizer.prompt"
        titleBarColor="#1E293B" editorBg="#0F172A">

        {/* Natural language section 1 */}
        <Sequence from={30}>
          <TypedLines lines={naturalLanguageLines1}
            font="Inter" fontSize={13} color="#CBD5E1"
            lineGlow={{ color: '#4A90D9', opacity: 0.03, blur: 20 }}
            charsPerFrame={2} startLine={1} />
        </Sequence>

        {/* Code block */}
        <Sequence from={120}>
          <CodeBlockBg
            y={200} height={200} bg="#1A1F2E"
            leftBorder={{ color: '#94A3B8', opacity: 0.3, width: 3 }}
            slideInDuration={15} />
          <Sequence from={20}>
            <TypedLines lines={codeLines}
              font="JetBrains Mono" fontSize={11} color="#94A3B8"
              charsPerFrame={2} startLine={9} />
          </Sequence>
        </Sequence>

        {/* Natural language section 2 */}
        <Sequence from={260}>
          <TypedLines lines={naturalLanguageLines2}
            font="Inter" fontSize={13} color="#CBD5E1"
            lineGlow={{ color: '#4A90D9', opacity: 0.03, blur: 20 }}
            charsPerFrame={2} startLine={19} />
        </Sequence>
      </EditorWindow>
    </Sequence>

    {/* Section labels */}
    <Sequence from={120}>
      <BracketLabel text="Intent (natural language)" color="#4A90D9"
        opacity={0.5} yRange={[120, 260]} x={1400} drawDuration={20} />
    </Sequence>
    <Sequence from={240}>
      <BracketLabel text="Critical algorithm (code)" color="#94A3B8"
        opacity={0.5} yRange={[280, 430]} x={1400} drawDuration={20} />
    </Sequence>
    <Sequence from={340}>
      <BracketLabel text="Constraints (natural language)" color="#4A90D9"
        opacity={0.5} yRange={[450, 560]} x={1400} drawDuration={20} />
    </Sequence>

    {/* Floating annotation */}
    <Sequence from={420}>
      <FadeIn duration={20}>
        <RichText x={960} y={920} align="center" font="Inter" size={14}
          color="#E2E8F0" opacity={0.6}>
          Stay in <Span color="#4A90D9">prompt space</Span> as long as possible.
          Dip into <Span color="#94A3B8">code</Span> when you must.
        </RichText>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "document_visualization",
  "filename": "ad_latency_optimizer.prompt",
  "sections": [
    {
      "type": "natural_language",
      "lines": "1-8",
      "label": "Intent (natural language)",
      "color": "#4A90D9"
    },
    {
      "type": "embedded_code",
      "lines": "9-18",
      "label": "Critical algorithm (code)",
      "color": "#94A3B8",
      "language": "python"
    },
    {
      "type": "natural_language",
      "lines": "19-24",
      "label": "Constraints (natural language)",
      "color": "#4A90D9"
    }
  ],
  "annotation": "Stay in prompt space as long as possible. Dip into code when you must.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_009"]
}
```

---
