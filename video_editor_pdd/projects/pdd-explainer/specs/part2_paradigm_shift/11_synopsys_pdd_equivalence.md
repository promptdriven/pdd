[Remotion]

# Section 2.11: Synopsys-PDD Equivalence — Specification In, Verified Artifact Out

**Tool:** Remotion
**Duration:** ~13s (390 frames @ 30fps)
**Timestamp:** 2:58 - 3:11

## Visual Description

A clean text overlay that draws the explicit parallel between chip design and PDD. Two lines appear in a balanced, typographic layout:

**Line 1:** "Synopsys: specification in → verified hardware out."
**Line 2:** "PDD: prompt in → verified software out."

The two lines are visually parallel — same structure, same layout, different domains. An arrow connects the concepts. Then a morphing animation: Verilog code on the left morphs into a glowing document labeled "PROMPT". A gate-level netlist on the right morphs into lines of software code. A Synopsys verification checkmark morphs into a test suite with green checkmarks.

The transition makes the analogy concrete — same architecture, different medium.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Text Overlay (Phase 1)
- Line 1: "Synopsys: specification in → verified hardware out." — Inter, 24px, bold (700), `#E2E8F0`
  - "Synopsys" highlighted `#4A90D9`
  - "→" as arrow icon, `#64748B` at 0.6
  - Centered at y: 440
- Line 2: "PDD: prompt in → verified software out." — Inter, 24px, bold (700), `#E2E8F0`
  - "PDD" highlighted `#4ADE80`
  - "→" as arrow icon, `#64748B` at 0.6
  - Centered at y: 520
- Connecting bracket: thin vertical line between the two, `#334155` at 0.3
- Shared label at right: "Same architecture" — Inter, 14px, italic, `#FBBF24` at 0.6

#### Morph Elements (Phase 2)
- LEFT morph: Verilog code block → glowing "PROMPT" document
  - Verilog: small code snippet, JetBrains Mono, `#C792EA` syntax
  - PROMPT: rounded rectangle with glow, `#4ADE80` at 0.4, labeled "PROMPT"
- CENTER morph: Synopsys checkmark → test suite checkmarks
  - Single large checkmark `#4A90D9` → three smaller checkmarks with "Tests" label `#4ADE80`
- RIGHT morph: gate-level netlist nodes → software code lines
  - Netlist: nodes and connections, `#4ADE80`
  - Code: horizontal lines representing code, `#94A3B8` at 0.4

### Animation Sequence
1. **Frame 0-60 (0-2s):** Line 1 types on: "Synopsys: specification in → verified hardware out."
2. **Frame 60-120 (2-4s):** Line 2 types on below: "PDD: prompt in → verified software out."
3. **Frame 120-180 (4-6s):** Connecting bracket appears. "Same architecture" label fades in. Hold.
4. **Frame 180-270 (6-9s):** Text fades to 0.3 opacity. Three morph pairs appear below:
   - LEFT: Verilog code morphs into PROMPT document
   - CENTER: checkmark morphs into test suite
   - RIGHT: netlist morphs into software code
5. **Frame 270-390 (9-13s):** Hold on completed morph. The three pairs sit side by side, showing the complete translation.

### Typography
- Comparison lines: Inter, 24px, bold (700), `#E2E8F0`
- Synopsys highlight: `#4A90D9`
- PDD highlight: `#4ADE80`
- Architecture label: Inter, 14px, italic, `#FBBF24` at 0.6
- Morph labels: Inter, 12px, `#94A3B8` at 0.5

### Easing
- Text type-on: linear, 2 frames per character
- Bracket draw: `easeOut(quad)` over 15 frames
- Label fade-in: `easeOut(quad)` over 20 frames
- Morph transitions: `easeInOut(cubic)` over 40 frames
- Text dim: `easeOut(quad)` over 15 frames

## Narration Sync
> "Synopsys turned hardware descriptions into verified silicon. PDD turns prompts into verified software. Same architecture. Specification in, verified artifact out."

Segment: `part2_paradigm_shift_017`

- **2:58** ("Synopsys turned hardware"): Line 1 types on
- **3:02** ("PDD turns prompts"): Line 2 types on
- **3:06** ("Same architecture"): Label appears, morphs begin

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={390}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Line 1 — Synopsys */}
    <Sequence from={0}>
      <TypeWriter
        parts={[
          { text: 'Synopsys', color: '#4A90D9' },
          { text: ': specification in ', color: '#E2E8F0' },
          { text: '→', color: '#64748B' },
          { text: ' verified hardware out.', color: '#E2E8F0' }
        ]}
        font="Inter" size={24} weight={700}
        x={960} y={440} align="center"
        charDelay={2} />
    </Sequence>

    {/* Line 2 — PDD */}
    <Sequence from={60}>
      <TypeWriter
        parts={[
          { text: 'PDD', color: '#4ADE80' },
          { text: ': prompt in ', color: '#E2E8F0' },
          { text: '→', color: '#64748B' },
          { text: ' verified software out.', color: '#E2E8F0' }
        ]}
        font="Inter" size={24} weight={700}
        x={960} y={520} align="center"
        charDelay={2} />
    </Sequence>

    {/* Connecting bracket + label */}
    <Sequence from={120}>
      <FadeIn duration={20}>
        <VerticalBracket x={1480} yTop={440} yBottom={520}
          color="#334155" opacity={0.3} width={1} />
        <Text text="Same architecture"
          font="Inter" size={14} style="italic"
          color="#FBBF24" opacity={0.6}
          x={1560} y={480} align="left" />
      </FadeIn>
    </Sequence>

    {/* Morph pairs */}
    <Sequence from={180}>
      <MorphPair
        fromElement={<VerilogSnippet />}
        toElement={<PromptDocument label="PROMPT" color="#4ADE80" />}
        position={[300, 700]}
        duration={40} />
      <MorphPair
        fromElement={<CheckmarkIcon color="#4A90D9" />}
        toElement={<TestSuiteIcons color="#4ADE80" count={3} />}
        position={[960, 700]}
        duration={40} />
      <MorphPair
        fromElement={<NetlistNodes color="#4ADE80" />}
        toElement={<CodeLines color="#94A3B8" />}
        position={[1620, 700]}
        duration={40} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "text_overlay_with_morph",
  "diagramId": "synopsys_pdd_equivalence",
  "comparisons": [
    {
      "domain": "Synopsys",
      "domainColor": "#4A90D9",
      "input": "specification",
      "output": "verified hardware"
    },
    {
      "domain": "PDD",
      "domainColor": "#4ADE80",
      "input": "prompt",
      "output": "verified software"
    }
  ],
  "morphPairs": [
    { "from": "verilog_code", "to": "prompt_document" },
    { "from": "synopsys_checkmark", "to": "test_suite" },
    { "from": "gate_netlist", "to": "software_code" }
  ],
  "sharedLabel": "Same architecture",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part2_paradigm_shift_017"]
}
```

---
