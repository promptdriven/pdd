[Remotion]

# Section 2.5: Synopsys ↔ PDD — Specification In, Verified Artifact Out

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 9:27 - 9:37

## Visual Description
A clean overlay that draws the explicit parallel between Synopsys chip synthesis and PDD software generation. A text overlay appears first: "Synopsys: specification in → verified hardware out." Then below it: "PDD: prompt in → verified software out." The two lines are visually aligned to emphasize the structural identity. Then the text morphs into a side-by-side diagram: LEFT shows Verilog code flowing through a synthesis engine to produce a gate-level netlist with a formal verification checkmark. RIGHT shows a prompt file flowing through an LLM generator to produce software code with a test suite checkmark. Matching arrows and structure make the parallel unmistakable.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Text Overlay Phase:**
  - Line 1: "Synopsys: specification in → verified hardware out" — `#2AA198` (teal) for "Synopsys" and "specification", `#FFFFFF` for the rest, 28px, centered at Y=420px
  - Line 2: "PDD: prompt in → verified software out" — `#4A90D9` (blue) for "PDD" and "prompt", `#FFFFFF` for the rest, 28px, centered at Y=480px
  - Arrow characters "→" in `#94A3B8`

- **Diagram Phase (two parallel pipelines):**
  - **Left Pipeline (Chip Synthesis) — centered at X=480:**
    - Input box: "Verilog HDL" — rounded rect 180x50px, `rgba(42,161,152,0.15)` fill, `#2AA198` 1px border, label in `#2AA198` 16px
    - Arrow: downward, `#94A3B8`, 2px, 40px tall
    - Process box: "Synthesis Engine" — rounded rect 200x50px, `rgba(42,161,152,0.08)` fill, `#2AA198` dashed 1px border, label in `#94A3B8` 14px
    - Arrow: downward, `#94A3B8`, 2px, 40px tall
    - Output box: "Gate-Level Netlist" — rounded rect 180x50px, `rgba(100,100,120,0.15)` fill, `#6B7280` 1px border, label in `#6B7280` 16px
    - Verification badge: Green circle 30px, checkmark, `#22C55E`, positioned right of output box. Label: "FEC Verified" in `#22C55E` 12px

  - **Right Pipeline (PDD) — centered at X=1440:**
    - Input box: "Prompt" — rounded rect 180x50px, `rgba(74,144,217,0.15)` fill, `#4A90D9` 1px border, label in `#4A90D9` 16px
    - Arrow: downward, `#94A3B8`, 2px, 40px tall
    - Process box: "LLM Generator" — rounded rect 200x50px, `rgba(74,144,217,0.08)` fill, `#4A90D9` dashed 1px border, label in `#94A3B8` 14px
    - Arrow: downward, `#94A3B8`, 2px, 40px tall
    - Output box: "Generated Code" — rounded rect 180x50px, `rgba(100,100,120,0.15)` fill, `#6B7280` 1px border, label in `#6B7280` 16px
    - Verification badge: Green circle 30px, checkmark, `#22C55E`, positioned right of output box. Label: "Tests Pass" in `#22C55E` 12px

  - **Connecting Label:** Centered between the two pipelines at Y=380px: "Same architecture." in `#FFFFFF` 20px, semi-bold

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Line 1 types in (word-by-word fade, not character-by-character): "Synopsys:" → "specification in" → "→" → "verified hardware out"
2. **Frame 40-80 (1.33-2.67s):** Line 2 types in below: "PDD:" → "prompt in" → "→" → "verified software out"
3. **Frame 80-120 (2.67-4.0s):** Hold both lines visible. The structural parallel sinks in
4. **Frame 120-160 (4.0-5.33s):** Both lines dissolve. The two pipeline diagrams materialize — left pipeline draws top-to-bottom (input → process → output), then right pipeline draws simultaneously
5. **Frame 160-220 (5.33-7.33s):** Arrows animate downward. Process boxes pulse briefly. Output boxes fill in. The flow direction is clear: spec → engine → artifact
6. **Frame 220-260 (7.33-8.67s):** Green verification badges scale in with `easeOut(back)` on both sides simultaneously. "FEC Verified" and "Tests Pass" labels fade in
7. **Frame 260-300 (8.67-10.0s):** "Same architecture." label fades in between the two pipelines. Hold. The point lands

### Typography
- Text overlay: Inter, 28px, regular (400), mixed colors (see above)
- Pipeline box labels: Inter, 16px, semi-bold (600)
- Process labels: Inter, 14px, regular (400), `#94A3B8`
- Verification labels: Inter, 12px, semi-bold (600), `#22C55E`
- "Same architecture": Inter, 20px, semi-bold (600), `#FFFFFF`

### Easing
- Word-by-word fade: `easeOut(quad)` per word, 8-frame intervals
- Text dissolve: `easeIn(quad)`
- Pipeline draw: `easeOut(cubic)` per element, top-to-bottom stagger
- Arrows: `easeOut(quad)`
- Verification badges: `easeOut(back(1.3))`
- "Same architecture" label: `easeOut(quad)`

## Narration Sync
> "Synopsys turned hardware descriptions into verified silicon. PDD turns prompts into verified software. Same architecture. Specification in, verified artifact out."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Text Overlay Phase */}
  <Sequence from={0} durationInFrames={120}>
    <WordByWordReveal
      text="Synopsys: specification in → verified hardware out"
      highlightWords={{ "Synopsys:": "#2AA198", "specification": "#2AA198" }}
      y={420}
    />
    <Sequence from={40}>
      <WordByWordReveal
        text="PDD: prompt in → verified software out"
        highlightWords={{ "PDD:": "#4A90D9", "prompt": "#4A90D9" }}
        y={480}
      />
    </Sequence>
  </Sequence>

  {/* Pipeline Diagrams */}
  <Sequence from={120} durationInFrames={180}>
    <PipelineDiagram
      x={480}
      input={{ label: "Verilog HDL", color: "#2AA198" }}
      process={{ label: "Synthesis Engine", color: "#2AA198" }}
      output={{ label: "Gate-Level Netlist", color: "#6B7280" }}
      verification={{ label: "FEC Verified", color: "#22C55E" }}
    />
    <PipelineDiagram
      x={1440}
      input={{ label: "Prompt", color: "#4A90D9" }}
      process={{ label: "LLM Generator", color: "#4A90D9" }}
      output={{ label: "Generated Code", color: "#6B7280" }}
      verification={{ label: "Tests Pass", color: "#22C55E" }}
    />
    <Sequence from={140}>
      <CenterLabel text="Same architecture." y={380} />
    </Sequence>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "textOverlay": {
    "line1": "Synopsys: specification in → verified hardware out",
    "line2": "PDD: prompt in → verified software out"
  },
  "leftPipeline": {
    "x": 480,
    "input": { "label": "Verilog HDL", "color": "#2AA198" },
    "process": { "label": "Synthesis Engine", "color": "#2AA198" },
    "output": { "label": "Gate-Level Netlist", "color": "#6B7280" },
    "verification": { "label": "FEC Verified", "color": "#22C55E" }
  },
  "rightPipeline": {
    "x": 1440,
    "input": { "label": "Prompt", "color": "#4A90D9" },
    "process": { "label": "LLM Generator", "color": "#4A90D9" },
    "output": { "label": "Generated Code", "color": "#6B7280" },
    "verification": { "label": "Tests Pass", "color": "#22C55E" }
  },
  "centerLabel": "Same architecture.",
  "backgroundColor": "#0F172A"
}
```

---
