[Remotion]

# Section 1.4: Context Window Shrink — The Growing Grid

**Tool:** Remotion
**Duration:** ~48s
**Timestamp:** 2:10 – 2:58

## Visual Description
A vivid visualization of the context window problem. A small 4x4 grid of code blocks starts on screen with a glowing blue rectangle ("context window") covering ~80% of it. The grid progressively grows — 4x4 → 8x8 → 16x16 → 32x32 — while the context window stays exactly the same size. A "Context Coverage" counter drops from 80% → 40% → 10% → 2%. Inside the tiny remaining window, some blocks highlight red (irrelevant code grabbed by AI) while green blocks outside the window show what was actually needed. A small inset graph shows "Performance vs. Context Length" with a steadily declining line.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F1923 (dark blue-black)
- No grid lines

### Chart/Visual Elements
- **Code grid:** Centered on screen. Each block is a rounded rectangle with monospace text texture (simulated code). Blocks are #1E293B with 1px border #2D3F55.
  - 4x4 phase: 16 blocks, each ~80x80px
  - 8x8 phase: 64 blocks, each ~40x40px
  - 16x16 phase: 256 blocks, each ~20x20px
  - 32x32 phase: 1024 blocks, each ~10x10px (appear as a dense mosaic)
- **Context window:** Glowing blue rectangle (#4A90D9 border, 3px, with 8px outer glow at 30% opacity). Fixed size: 300×300px. Stays centered as grid grows around it.
- **Coverage counter:** Top-right corner. Large number with "Context Coverage" label. Animates with counting effect.
- **Red-highlighted blocks (inside window):** #EF4444 at 40% opacity — irrelevant code the AI grabbed
- **Green-highlighted blocks (outside window):** #22C55E at 40% opacity — needed code the AI missed
- **Performance inset graph (appears late):** 300×180px, bottom-right corner. Simple line chart: X = "Context Length", Y = "Performance". Line drops steadily. Label: "14–85% degradation (EMNLP, 2025)"
- **"Context Rot" label:** Appears after performance graph, with a subtle glitch/static effect on the text

### Animation Sequence
1. **Frame 0–45 (0–1.5s):** 4x4 grid fades in, block by block (staggered, 2 frames per block). Context window appears with a glow pulse. Coverage counter shows "80%".
2. **Frame 45–120 (1.5–4s):** Hold at 4x4. Context window glows warmly. Synced with "When your codebase is small, AI tools are brilliant..."
3. **Frame 120–180 (4–6s):** Grid morphs from 4x4 → 8x8 with a smooth scale transition. Each block subdivides into 4 smaller blocks. Context window stays exactly the same size. Counter animates: 80% → 40%. Brief screen shake (2px, 200ms) on the transition.
4. **Frame 180–240 (6–8s):** Grid morphs 8x8 → 16x16. Counter: 40% → 10%. The window looks noticeably small now. Synced with "But codebases grow. And that window? It stays the same size."
5. **Frame 240–300 (8–10s):** Grid morphs 16x16 → 32x32. Counter: 10% → 2%. The grid is now a dense mosaic and the window is a tiny rectangle in the middle. Counter number turns red.
6. **Frame 300–480 (10–16s):** Hold at 32x32. Inside the window, 3–4 blocks flash red (irrelevant code). Outside, 6–8 blocks flash green (needed code). Visual tension between what AI sees and what it needs. Synced with "So now the AI has to guess what's relevant..."
7. **Frame 480–720 (16–24s):** Blocks outside the window that are green get subtle arrow/line indicators pointing toward the window — "wanted but unreachable." Synced with description of Cursor embeddings, Claude Code agentic search, Jolt AI benchmarks.
8. **Frame 720–960 (24–32s):** Performance inset graph draws on in the bottom-right. Line drops steadily from left to right. "14–85% degradation" annotation appears. Synced with "even when the model retrieves the right information, performance still degrades..."
9. **Frame 960–1200 (32–40s):** "Context Rot" text appears large, center-bottom of screen with a digital glitch/static effect — letters briefly scramble then resolve. The whole grid dims slightly except the context window, which flickers. Synced with "they call it context rot."
10. **Frame 1200–1440 (40–48s):** Hold and slowly dissolve. The grid pattern fades, leaving only the tiny context window floating in darkness before it too fades.

### Typography
- Coverage counter number: Inter Bold, 72px, #FFFFFF (turns #EF4444 below 10%)
- Coverage counter label: Inter Regular, 16px, #8B9DC3
- Performance graph title: Inter Medium, 14px, #8B9DC3
- Performance annotation: Inter Regular, 12px, #F59E0B (warning orange)
- "Context Rot" text: Space Grotesk Bold, 48px, #EF4444, with glitch effect

### Easing
- Grid growth: `easeInOutCubic` (800ms per phase)
- Counter decrement: `easeOutExpo`
- Block highlight flash: `easeInOutSine` (pulse loop, 1.5s period)
- Performance line draw: `easeInOutCubic`
- Glitch effect: random jitter, 4 frames

## Narration Sync
> "But there's a second kind of debt hiding in there. One that's specific to AI-assisted development."

> "When your codebase is small, AI tools are brilliant. The context window — what the model can actually see — covers almost everything. It understands how the pieces connect."

> "But codebases grow. And that window? It stays the same size. A typical enterprise codebase spans millions of tokens. Even the largest context windows hold a fraction of that."

> "So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search — grep, file by file."

> "And it gets worse. A 2025 EMNLP study proved that even when the model retrieves the right information, performance still degrades — fourteen to eighty-five percent — just from the sheer length of the input... they call it context rot."

Segments: `part1_economics_017` (150.08s – 155.70s) through `part1_economics_021` (203.86s – 235.74s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1440}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    {/* Growing code grid */}
    <GrowingCodeGrid
      phases={[
        { size: 4, startFrame: 0, endFrame: 120 },
        { size: 8, startFrame: 120, endFrame: 180 },
        { size: 16, startFrame: 180, endFrame: 240 },
        { size: 32, startFrame: 240, endFrame: 1440 },
      ]}
    />

    {/* Fixed-size context window */}
    <ContextWindowOverlay
      width={300}
      height={300}
      glowColor="#4A90D9"
    />

    {/* Coverage counter */}
    <CoverageCounter
      keyframes={[
        { frame: 0, value: 80 },
        { frame: 150, value: 40 },
        { frame: 210, value: 10 },
        { frame: 270, value: 2 },
      ]}
    />

    {/* Highlighted blocks (relevant/irrelevant) */}
    <Sequence from={300} durationInFrames={420}>
      <HighlightedBlocks
        insideWindow={redBlocks}
        outsideWindow={greenBlocks}
      />
    </Sequence>

    {/* Performance inset graph */}
    <Sequence from={720} durationInFrames={240}>
      <PerformanceInsetGraph
        degradationRange="14-85%"
        source="EMNLP, 2025"
      />
    </Sequence>

    {/* Context Rot label */}
    <Sequence from={960} durationInFrames={240}>
      <GlitchText text="Context Rot" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "coveragePhases": [
    { "gridSize": "4x4", "blocks": 16, "coverage": 80 },
    { "gridSize": "8x8", "blocks": 64, "coverage": 40 },
    { "gridSize": "16x16", "blocks": 256, "coverage": 10 },
    { "gridSize": "32x32", "blocks": 1024, "coverage": 2 }
  ],
  "performanceDegradation": {
    "source": "EMNLP, 2025",
    "rangeMin": 14,
    "rangeMax": 85,
    "unit": "percent",
    "cause": "context length alone"
  },
  "retrievalMethods": [
    { "tool": "Cursor", "method": "embeddings", "accuracy": "low" },
    { "tool": "Claude Code", "method": "agentic search", "accuracy": "higher", "latency": "3-5 min/query" }
  ],
  "chromaStudy": {
    "modelsTestedCount": 18,
    "finding": "context rot confirmed"
  }
}
```
