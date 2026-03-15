[split:]

# Section 1.7: Agentic Patching vs. PDD Regeneration — Context Split

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 3:55 - 4:09

## Visual Description
A split-screen comparison showing the contrast between agentic patching and PDD regeneration at the context-window level. LEFT panel ("Agentic Patching"): a context window filled with ~15,000 tokens of code — noisy, with red-highlighted irrelevant sections and a tiny green sliver of relevant code. RIGHT panel ("PDD Regeneration"): a context window with a compact 300-token prompt, 2,000 tokens of tests, and a small grounding example — clean, focused, with visible room to spare. The visual contrast is immediate and powerful. Then 20 code blocks try to fit into a context window and overflow; the same 20 blocks compress into prompts and fit with room to spare.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Outer background `#0A1628`
- Grid lines: None

### Chart/Visual Elements
- **Left Panel:** Width 940px, background `#111827`
  - Header: "Agentic Patching" in `#FFFFFF`, 24px semi-bold, top-center of panel
  - Context Window Representation: Rounded rectangle 400x600px, border `rgba(239,68,68,0.4)`, border-radius 8px
    - Fill: Packed with horizontal lines representing code tokens (monospace texture at varying opacities 0.1–0.3)
    - Red highlights: 4-5 rectangular blocks (irrelevant code) — `rgba(239,68,68,0.2)` fill, scattered throughout
    - Green highlight: 1 small block (relevant code) — `rgba(34,197,94,0.3)`, tiny, at about 70% down
    - Token counter: "~15,000 tokens" at bottom, `#94A3B8`, 14px
  - Label below: "Noisy. Guessing." in `#EF4444`, 16px italic
- **Right Panel:** Width 940px, background `#0F1B2E`
  - Header: "PDD Regeneration" in `#FFFFFF`, 24px semi-bold, top-center of panel
  - Context Window Representation: Same 400x600px rounded rectangle, border `rgba(74,144,217,0.4)`, border-radius 8px
    - Prompt Block: Compact rectangle at top, `rgba(74,144,217,0.15)` fill, 80px tall, label "Prompt (~300 tokens)"
    - Test Block: Below prompt, `rgba(217,148,74,0.15)` fill, 140px tall, label "Tests (~2,000 tokens)"
    - Grounding Block: Below tests, `rgba(90,170,110,0.15)` fill, 60px tall, label "Grounding example"
    - Empty Space: Remaining ~320px of the window is empty — `rgba(255,255,255,0.02)` subtle checkerboard to emphasize emptiness
    - Token counter: "~2,500 tokens" at bottom, `#94A3B8`, 14px
  - Label below: "Clean. Focused. Room to think." in `#4A90D9`, 16px italic
- **Vertical Divider:** 2px wide, white `#FFFFFF` at 0.15 opacity, centered at X=960
- **Phase 2 — Module Compression Animation (post-split):**
  - 20 code blocks (small rectangles, `#1E293B` with code texture) attempt to enter a context-window rectangle. They overflow — blocks spill out
  - Blocks compress into 20 compact prompt blocks (`rgba(74,144,217,0.2)`, 1/5 height each). All fit with room to spare
  - Label: "Same system. 5-10x more fits." in `#FFFFFF`, 20px

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Both panels slide in — left from left edge, right from right edge. Divider appears
2. **Frame 15-35 (0.5-1.17s):** "Agentic Patching" and "PDD Regeneration" headers fade in
3. **Frame 35-90 (1.17-3.0s):** Left context window draws in. Code lines fill it up rapidly. Then red highlights pulse in across the window (irrelevant code). Tiny green block appears last — barely visible
4. **Frame 90-150 (3.0-5.0s):** Right context window draws in. Prompt block slides down from top. Test block slides in below. Grounding block appears. Large empty area remains. The visual breathing room is palpable
5. **Frame 150-180 (5.0-6.0s):** Token counters fade in simultaneously: "~15,000" vs "~2,500". Labels fade in: "Noisy. Guessing." vs "Clean. Focused. Room to think."
6. **Frame 180-230 (6.0-7.67s):** Hold the split comparison for emphasis
7. **Frame 230-290 (7.67-9.67s):** Split fades down. 20 code blocks appear, try to enter a single context-window frame. They overflow and pile up outside
8. **Frame 290-370 (9.67-12.33s):** Code blocks morph/compress into 20 compact prompt blocks (each shrinks to 1/5 height, color shifts blue). All slide into the context window with room to spare
9. **Frame 370-420 (12.33-14.0s):** "Same system. 5-10x more fits." label fades in. Hold

### Typography
- Panel Headers: Inter, 24px, semi-bold (600), `#FFFFFF`
- Block Labels: Inter, 13px, regular (400), `#94A3B8`
- Token Counters: Inter, 14px, regular (400), `#94A3B8`
- Bottom Labels: Inter, 16px, italic (400)
- Compression Label: Inter, 20px, semi-bold (600), `#FFFFFF`

### Easing
- Panel slide-in: `easeOut(cubic)`
- Code lines fill: `linear` (rapid sequential)
- Red/green highlight: `easeOut(quad)`
- Block slide-in (right): `easeOut(quad)` with 10-frame staggers
- Token counter fade: `easeOut(quad)`
- Code block overflow: `easeIn(quad)` (accelerating pile-up)
- Compression morph: `easeInOut(cubic)`
- Prompt block slide-in: `easeOut(back(1.1))`

## Narration Sync
> "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs."
> "And there's something else. These models are trained on up to thirty times more natural language than code. Natural language is their deepest fluency."
> "We saw this firsthand. A team optimizing ad delivery latency had twenty modules on the critical path. As code, they overflowed the context window. As prompts — a fifth to a tenth the size — they all fit."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Split Panels */}
  <Sequence from={0} durationInFrames={230}>
    {/* Left Panel — Agentic Patching */}
    <SplitPanel side="left" background="#111827">
      <PanelHeader text="Agentic Patching" />
      <ContextWindowViz
        border="rgba(239,68,68,0.4)"
        codeLines={150}
        redHighlights={5}
        greenHighlights={1}
        tokenCount="~15,000 tokens"
      />
      <PanelLabel text="Noisy. Guessing." color="#EF4444" />
    </SplitPanel>

    {/* Divider */}
    <VerticalDivider x={960} opacity={0.15} />

    {/* Right Panel — PDD Regeneration */}
    <SplitPanel side="right" background="#0F1B2E">
      <PanelHeader text="PDD Regeneration" />
      <ContextWindowViz border="rgba(74,144,217,0.4)">
        <PromptBlock height={80} label="Prompt (~300 tokens)" />
        <TestBlock height={140} label="Tests (~2,000 tokens)" />
        <GroundingBlock height={60} label="Grounding example" />
        <EmptySpace height={320} />
      </ContextWindowViz>
      <PanelLabel text="Clean. Focused. Room to think." color="#4A90D9" />
    </SplitPanel>
  </Sequence>

  {/* Module Compression Animation */}
  <Sequence from={230} durationInFrames={190}>
    <ModuleCompressionAnimation
      moduleCount={20}
      codeBlockHeight={40}
      promptBlockHeight={8}
      contextWindowHeight={200}
      label="Same system. 5-10× more fits."
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "leftPanel": {
    "title": "Agentic Patching",
    "background": "#111827",
    "tokenCount": 15000,
    "redHighlights": 5,
    "greenHighlights": 1,
    "label": "Noisy. Guessing.",
    "labelColor": "#EF4444",
    "borderColor": "rgba(239, 68, 68, 0.4)"
  },
  "rightPanel": {
    "title": "PDD Regeneration",
    "background": "#0F1B2E",
    "blocks": [
      { "type": "prompt", "tokens": 300, "height": 80, "color": "rgba(74, 144, 217, 0.15)" },
      { "type": "tests", "tokens": 2000, "height": 140, "color": "rgba(217, 148, 74, 0.15)" },
      { "type": "grounding", "tokens": 200, "height": 60, "color": "rgba(90, 170, 110, 0.15)" }
    ],
    "totalTokens": 2500,
    "label": "Clean. Focused. Room to think.",
    "labelColor": "#4A90D9",
    "borderColor": "rgba(74, 144, 217, 0.4)"
  },
  "compression": {
    "moduleCount": 20,
    "compressionRatio": "5-10×",
    "label": "Same system. 5-10× more fits."
  },
  "backgroundColor": "#0A1628"
}
```

---
