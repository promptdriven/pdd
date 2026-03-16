[split:]

# Section 1.6: Split-Screen Context Comparison

**Tool:** Remotion
**Duration:** ~36s
**Timestamp:** 3:28 – 4:04

## Visual Description
A split-screen comparison showing the fundamental advantage of PDD regeneration over agentic patching. LEFT side: "Agentic Patching" — a context window crammed with ~15,000 tokens of code, red highlights on irrelevant sections, a tiny green section with the relevant code buried in noise. RIGHT side: "PDD Regeneration" — a clean context window with a 300-token prompt, 2,000 tokens of tests, and a small grounding example. The contrast is stark: chaotic vs. clean, noisy vs. focused. An animation of 20 code blocks trying to fit into a context window (and overflowing) then compressing into 20 compact prompt blocks (all fitting with room to spare) reinforces the point.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F1923 (dark blue-black)
- Vertical divider: 2px, #FFFFFF at 20% opacity, centered

### Chart/Visual Elements
- **Left panel ("Agentic Patching"):**
  - Header: "Agentic Patching" with Cursor/Claude Code icon silhouettes
  - Context window representation: 800×500px rectangle, #1E293B background
  - Filled with ~40 small code blocks (simulated syntax-highlighted text)
  - Red-highlighted blocks (70% of them): #EF4444 at 20% opacity — irrelevant code
  - Green-highlighted block (1 small block): #22C55E at 30% opacity — the actual relevant code, nearly invisible in the noise
  - Token counter: "~15,000 tokens" in bottom-left of panel
  - Visual noise: blocks are packed tight, overlapping slightly, creating visual chaos
  - Small "3–5 min search" timer icon in corner

- **Right panel ("PDD Regeneration"):**
  - Header: "PDD Regeneration" with PDD logo silhouette
  - Context window representation: 800×500px rectangle, #1E293B background
  - Three clean sections, well-spaced:
    - Prompt block: #4A90D9 border, ~300 tokens, labeled "Prompt (300 tokens)"
    - Test block: #D9944A border, ~2,000 tokens, labeled "Tests (2,000 tokens)"
    - Grounding block: #8B5CF6 border, small, labeled "Example (500 tokens)"
  - Large empty area labeled "Room to think" in faded text
  - Token counter: "~2,800 tokens" in bottom-left
  - Visual calm: clean spacing, breathing room, no clutter

- **Module overflow animation (appears mid-sequence):**
  - 20 colored blocks labeled "Module 1" through "Module 20"
  - First attempt: blocks try to fit into a code-sized window → overflow, stack up, fall off edges
  - Second attempt: blocks compress (shrink to 1/5–1/10 size) → all fit with room to spare
  - Label: "Same system. 5–10× more fits."

### Animation Sequence
1. **Frame 0–30 (0–1s):** Vertical divider draws top-to-bottom. Panel headers fade in. Left: warm red tint. Right: cool blue tint.
2. **Frame 30–150 (1–5s):** Left panel: code blocks rapidly fill the context window, one after another, creating visual clutter. Token counter ticks up quickly. Synced with "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size..."
3. **Frame 150–300 (5–10s):** Right panel: three clean sections slide in with spring physics, spaced generously. Token counter shows 2,800. "Room to think" text fades in the empty space. Synced with "the prompts for ten modules fit comfortably... No retrieval. No search. No rot."
4. **Frame 300–450 (10–15s):** Left panel: red highlights pulse on irrelevant blocks. The single green block gets a spotlight circle briefly, then it's lost again in the noise. 3–5 min timer animates.
5. **Frame 450–600 (15–20s):** Both panels hold for comparison. A "vs." badge pulses at the center divider.
6. **Frame 600–780 (20–26s):** Split screen dissolves. 20 code blocks appear as a horizontal row. They try to squeeze into a window outline → overflow and stack chaotically.
7. **Frame 780–900 (26–30s):** The 20 blocks compress smoothly (scale down with spring) into 20 prompt-sized blocks. They all fit inside the same window with visible space remaining. Label "Same system. 5–10× more fits." fades in.
8. **Frame 900–1080 (30–36s):** Hold on compressed view. The remaining space inside the window glows subtly blue — "room to think."

### Typography
- Panel headers: Inter Bold, 24px, #FFFFFF
- Token counters: Space Mono, 16px, left panel #EF4444, right panel #22C55E
- Section labels (prompt/tests/example): Inter Medium, 14px, matching border color
- "Room to think": Inter Regular, 18px, #4A90D9 at 30% opacity
- "Same system" label: Inter SemiBold, 22px, #FFFFFF
- "vs." badge: Inter Black, 20px, #FFFFFF, circular background #2D3F55

### Easing
- Divider draw: `easeInOutCubic`
- Code block rapid fill: `easeOutQuad` (staggered, 50ms per block)
- Clean section slide-in: `spring({ damping: 14, stiffness: 110 })`
- Module compression: `spring({ damping: 18, stiffness: 140 })`
- Token counter tick: `easeOutExpo`

## Narration Sync
> "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs. So where raw code overwhelms the context window, the prompts for ten modules fit comfortably. And the prompt defines its own context — the developer declares exactly what the model needs to see, instead of an agentic tool guessing at what's relevant. No retrieval. No search. No rot."

> "And there's something else. These models are trained on up to thirty times more natural language than code. Natural language is their deepest fluency. MIT showed that giving models natural language context for coding tasks improved performance by up to eighty-nine percent."

> "We saw this firsthand. A team optimizing ad delivery latency had twenty modules on the critical path. As code, they overflowed the context window... As prompts — a fifth to a tenth the size — they all fit."

Segments: `part1_economics_026` through `part1_economics_029`

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1080}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    {/* Vertical divider */}
    <Sequence from={0} durationInFrames={30}>
      <DrawOnDivider />
    </Sequence>

    {/* Left panel: Agentic Patching */}
    <Sequence from={30} durationInFrames={420}>
      <LeftPanel>
        <PanelHeader text="Agentic Patching" tint="red" />
        <ClutteredContextWindow
          blockCount={40}
          irrelevantRatio={0.7}
          tokenCount={15000}
        />
      </LeftPanel>
    </Sequence>

    {/* Right panel: PDD Regeneration */}
    <Sequence from={150} durationInFrames={300}>
      <RightPanel>
        <PanelHeader text="PDD Regeneration" tint="blue" />
        <CleanContextWindow
          sections={[
            { label: "Prompt", tokens: 300, color: "#4A90D9" },
            { label: "Tests", tokens: 2000, color: "#D9944A" },
            { label: "Example", tokens: 500, color: "#8B5CF6" },
          ]}
          totalTokens={2800}
        />
      </RightPanel>
    </Sequence>

    {/* Module overflow → compression animation */}
    <Sequence from={600} durationInFrames={300}>
      <ModuleOverflowAnimation
        moduleCount={20}
        compressionRatio={0.15}
      />
    </Sequence>

    {/* "Same system" label */}
    <Sequence from={780} durationInFrames={300}>
      <FadeIn>
        <Label text="Same system. 5–10× more fits." />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "agenticPatching": {
    "tokenCount": 15000,
    "relevantCodeRatio": 0.05,
    "irrelevantCodeRatio": 0.70,
    "searchTime": "3-5 min per query"
  },
  "pddRegeneration": {
    "promptTokens": 300,
    "testTokens": 2000,
    "groundingTokens": 500,
    "totalTokens": 2800,
    "compressionRatio": "5-10x smaller"
  },
  "realWorldExample": {
    "team": "ad delivery latency",
    "moduleCount": 20,
    "asCode": "overflowed context window",
    "asPrompts": "all fit with room to spare",
    "result": "beat half-millisecond latency target"
  },
  "mitStudy": {
    "naturalLanguageImprovement": "up to 89%",
    "trainingRatio": "30x more natural language than code"
  }
}
```
