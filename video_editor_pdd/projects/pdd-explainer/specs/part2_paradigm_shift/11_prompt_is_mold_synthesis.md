[Remotion]

# Section 2.11: Prompt Is Mold — Code Is Just Plastic

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 10:53 - 11:07

## Visual Description
The closing visual for Part 2 crystallizes the central thesis. A glowing prompt document sits at center-left, pulsing with warm amber energy. From its right edge, streams of code flow outward — lines of generated text that pour into a defined shape, like liquid filling a mold cavity. The shape is bounded by test walls: vertical constraint lines that appear as the code fills, labeled with test names. The code fills the cavity exactly, constrained by the walls. When the cavity is full, a brief flash and the "part" solidifies. Then a subtitle pair appears: "The prompt is your mold." (amber) above "The code is just plastic." (blue-gray, dimmer). A final beat: the solidified code fades to low opacity while the prompt stays bright — driving home that the prompt is the durable asset, not the code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Prompt Document (Left)**
  - Position: centered at (300, 440)
  - Rounded rectangle 240px x 300px, border `#D9944A` 2px, fill `rgba(217,148,74,0.06)`
  - Header: "PROMPT" — `#D9944A`, 18px, bold
  - Content: 8 lines of natural language text, `#CBD5E1` at 0.5, 12px
  - Pulsing glow: `rgba(217,148,74,0.15)` radial, radius 200px, oscillating
- **Code Stream**
  - Particles/lines flowing from prompt's right edge (X=420) rightward to cavity at X=600-1300
  - Stream: 40+ small horizontal bars (code line representations), 60-120px wide x 3px tall
  - Color: `#4A90D9` at 0.4, with leading edge brighter at 0.7
  - Flow direction: left-to-right, slight vertical spread
- **Mold Cavity (Right)**
  - Position: X=600 to X=1300, Y=240 to Y=640
  - Inner area: transparent (code fills this space)
  - No outer wall visible — walls are the test constraints
- **Test Walls (Constraints)**
  - 6 vertical/horizontal wall segments bounding the cavity:
    - Top wall: Y=240, X=600 to X=1300, 3px, `#2AA198`
    - Bottom wall: Y=640, X=600 to X=1300, 3px, `#2AA198`
    - Right wall: X=1300, Y=240 to Y=640, 3px, `#2AA198`
    - Internal walls: 2-3 horizontal partitions at Y=340, Y=440, Y=540, partial width
  - Wall labels (small, attached to each wall):
    - "null_handling" — `#2AA198`, 11px
    - "edge_cases" — `#2AA198`, 11px
    - "performance" — `#2AA198`, 11px
    - "type_safety" — `#2AA198`, 11px
- **Solidified Code**
  - When cavity fills: code bars settle into final positions, opacity increases to 0.7
  - Brief white flash (`rgba(255,255,255,0.1)`) across the filled cavity
- **Subtitle Pair**
  - Line 1: "The prompt is your mold." — `#D9944A`, 28px, bold, centered at (960, 780)
  - Line 2: "The code is just plastic." — `#4A90D9` at 0.5, 22px, regular, centered at (960, 820)
- **Final Dimming**
  - Code in cavity fades to 0.15 opacity
  - Prompt document stays at full brightness
  - Visual hierarchy: prompt is the durable asset

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Prompt document fades in with border draw. Header and content lines appear. Pulsing glow begins
2. **Frame 40-60 (1.33-2s):** First test walls draw in — top, bottom, right constraints appear with their labels
3. **Frame 60-90 (2-3s):** Internal wall partitions draw in. All 6 wall segments now visible
4. **Frame 90-200 (3-6.67s):** Code stream begins flowing from prompt's right edge into the cavity. Bars enter from the left, spread vertically, and settle into position within the walls. Flow accelerates as cavity fills. Bars that hit walls stop and stack
5. **Frame 200-230 (6.67-7.67s):** Cavity fully filled. Brief white flash. All code bars solidify (opacity snap to 0.7). Stream stops
6. **Frame 230-280 (7.67-9.33s):** Hold — filled cavity with glowing prompt and test walls
7. **Frame 280-330 (9.33-11s):** Subtitle line 1 "The prompt is your mold." fades in. 15 frames later, line 2 "The code is just plastic." fades in below it
8. **Frame 330-380 (11-12.67s):** Code in cavity dims from 0.7 to 0.15 opacity over 50 frames. Prompt stays bright. Test walls stay visible at 0.6 opacity
9. **Frame 380-420 (12.67-14s):** Hold at final state — prompt glowing, code dimmed, walls standing

### Typography
- Prompt Header: Inter, 18px, bold (700), `#D9944A`
- Prompt Content: JetBrains Mono, 12px, regular (400), `#CBD5E1` at 0.5
- Wall Labels: JetBrains Mono, 11px, regular (400), `#2AA198`
- Subtitle Line 1: Inter, 28px, bold (700), `#D9944A`
- Subtitle Line 2: Inter, 22px, regular (400), `#4A90D9` at 0.5

### Easing
- Prompt fade-in: `easeOut(quad)`
- Wall draw: `easeOut(cubic)` per segment, staggered 8 frames apart
- Code stream flow: `easeIn(quad)` (accelerating fill)
- Code bar settle: `easeOut(back(1.1))` per bar
- Flash: `easeOut(expo)` (sharp fade)
- Subtitle fade: `easeOut(quad)`
- Code dimming: `easeInOut(cubic)`
- Prompt glow pulse: `easeInOut(sine)` (looping, 60-frame cycle)

## Narration Sync
> "The prompt is your mold. The code is just plastic. And just like chip synthesis — the code is different every generation. But the tests lock the behavior. The process is deterministic."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Prompt Document */}
  <Sequence from={0} durationInFrames={40}>
    <PromptDocument
      x={300} y={440} width={240} height={300}
      header="PROMPT" borderColor="#D9944A"
      glowColor="rgba(217,148,74,0.15)"
      pulsing
    />
  </Sequence>

  {/* Test Walls */}
  <Sequence from={40} durationInFrames={50}>
    <TestWalls
      bounds={{ x: 600, y: 240, width: 700, height: 400 }}
      color="#2AA198"
      labels={["null_handling", "edge_cases", "performance", "type_safety"]}
    />
  </Sequence>

  {/* Code Stream */}
  <Sequence from={90} durationInFrames={140}>
    <CodeStream
      fromX={420} toX={1300}
      cavityBounds={{ x: 600, y: 240, width: 700, height: 400 }}
      barCount={40}
      barColor="#4A90D9"
    />
  </Sequence>

  {/* Solidification Flash */}
  <Sequence from={200} durationInFrames={30}>
    <SolidificationFlash color="rgba(255,255,255,0.1)" />
  </Sequence>

  {/* Subtitle Pair */}
  <Sequence from={280} durationInFrames={50}>
    <FadeInLabel text="The prompt is your mold." y={780} color="#D9944A" fontSize={28} bold />
  </Sequence>
  <Sequence from={295} durationInFrames={35}>
    <FadeInLabel text="The code is just plastic." y={820} color="rgba(74,144,217,0.5)" fontSize={22} />
  </Sequence>

  {/* Code Dimming */}
  <Sequence from={330} durationInFrames={50}>
    <OpacityTransition target="codeInCavity" from={0.7} to={0.15} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "prompt": {
    "position": { "x": 300, "y": 440 },
    "size": { "width": 240, "height": 300 },
    "header": "PROMPT",
    "borderColor": "#D9944A",
    "fillColor": "rgba(217,148,74,0.06)",
    "glowColor": "rgba(217,148,74,0.15)",
    "glowRadius": 200,
    "contentLines": 8
  },
  "codeStream": {
    "fromX": 420,
    "barCount": 40,
    "barWidthRange": [60, 120],
    "barHeight": 3,
    "color": "#4A90D9",
    "leadingOpacity": 0.7,
    "trailingOpacity": 0.4
  },
  "testWalls": {
    "bounds": { "x": 600, "y": 240, "width": 700, "height": 400 },
    "wallWidth": 3,
    "color": "#2AA198",
    "labels": ["null_handling", "edge_cases", "performance", "type_safety"],
    "internalPartitions": [
      { "y": 340, "widthPercent": 0.6 },
      { "y": 440, "widthPercent": 0.8 },
      { "y": 540, "widthPercent": 0.5 }
    ]
  },
  "subtitles": {
    "line1": { "text": "The prompt is your mold.", "color": "#D9944A", "fontSize": 28 },
    "line2": { "text": "The code is just plastic.", "color": "rgba(74,144,217,0.5)", "fontSize": 22 }
  },
  "dimming": {
    "codeFromOpacity": 0.7,
    "codeToOpacity": 0.15
  }
}
```

---
