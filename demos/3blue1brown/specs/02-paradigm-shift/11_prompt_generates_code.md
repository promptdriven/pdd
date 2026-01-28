# Section 2.11: Prompt Generates Code (Tests as Walls)

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 7:25 - 7:40

## Visual Description

The prompt document pulses. Code flows out of it, filling a defined shape. Tests appear as walls around the code, constraining it. This previews Part 3's detailed explanation of the three components.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continues from Section 2.10

### Visual Elements

1. **The Prompt Document**
   - Position: Top-center or left-center
   - Blue glow (#4A90D9)
   - Pulses when generating

2. **Code Flow**
   - Flows from prompt like liquid
   - Lines of code (or abstract representation)
   - Fills a container shape
   - Color: Gray (#A0A0A0) - neutral

3. **Test Walls**
   - Appear as boundaries/constraints
   - Amber color (#D9944A)
   - Code stops when it hits a wall
   - Labels on walls: test conditions

4. **Container Shape**
   - Abstract shape defined by test walls
   - Code fills the interior
   - Clear boundary between inside/outside

### Animation Sequence

1. **Frame 0-60 (0-2s):** Prompt pulses
   - Blue glow intensifies
   - "Activating" animation
   - Ready to generate

2. **Frame 60-150 (2-5s):** Code begins flowing
   - Liquid-like stream from prompt
   - Flows toward center/right of screen
   - Free-form initially

3. **Frame 150-270 (5-9s):** Test walls appear
   - Walls materialize as code approaches
   - Each wall labeled with constraint:
     - "null → None"
     - "handles unicode"
     - "no exceptions"
     - "valid format required"
   - Code flow constrained by walls

4. **Frame 270-360 (9-12s):** Code fills container
   - Constrained by walls
   - Takes exact shape defined by tests
   - Settles into final form

5. **Frame 360-450 (12-15s):** Final state
   - Prompt glowing (value here)
   - Tests/walls glowing (value here)
   - Code filled but not glowing (just output)
   - Clear hierarchy

### Test Wall Specifications

```typescript
const TestWall = ({ label, position, angle }) => (
  <g transform={`translate(${position.x}, ${position.y}) rotate(${angle})`}>
    {/* Wall bar */}
    <rect
      width={120}
      height={8}
      fill="#D9944A"
      rx={2}
    />
    {/* Label */}
    <text
      x={60}
      y={-10}
      textAnchor="middle"
      fill="#FFF"
      fontSize={12}
      fontFamily="JetBrains Mono"
    >
      {label}
    </text>
  </g>
);
```

### Code Flow Specifications

- Particles or line segments flowing
- Liquid-like behavior
- Constrained by walls (collision detection)
- Fills available space

Options for visualization:
1. **Particle flow:** Dots that accumulate
2. **Line stream:** Code lines that stack
3. **Liquid fill:** Abstract liquid animation
4. **Text appearance:** Actual code text fading in

### Color Coding (Establishing Part 3 Palette)

| Element | Color | Meaning |
|---------|-------|---------|
| Prompt | Blue (#4A90D9) | Intent/specification |
| Tests | Amber (#D9944A) | Constraints/walls |
| Code | Gray (#A0A0A0) | Output/disposable |

### Glow Rules

- Prompt: GLOWS (value)
- Tests: GLOW (value)
- Code: NO GLOW (just output)

This reinforces: value is in the specification (prompt + tests), not the output (code).

## Narration Sync

> "The prompt is your mold. The code is just plastic."

These closing lines of Part 2 land as the visual completes.

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Prompt activation */}
  <Sequence from={0} durationInFrames={60}>
    <PromptDocument pulsing={true} />
  </Sequence>

  {/* Code flow */}
  <Sequence from={60}>
    <CodeFlow
      source="prompt"
      direction="right"
      liquidBehavior={true}
    />
  </Sequence>

  {/* Test walls appear */}
  <Sequence from={150}>
    <TestWall label="null → None" position={{x: 400, y: 200}} />
    <TestWall label="handles unicode" position={{x: 500, y: 300}} />
    <TestWall label="no exceptions" position={{x: 400, y: 400}} />
    <TestWall label="valid format" position={{x: 300, y: 300}} />
  </Sequence>

  {/* Final glow state */}
  <Sequence from={360}>
    <PromptGlow intensity="high" />
    <TestWallsGlow intensity="medium" />
    {/* Code notably does NOT glow */}
  </Sequence>
</Sequence>
```

## Visual Style Notes

- This is the setup for Part 3's detailed breakdown
- Should feel complete but also "there's more to explain"
- Clean, elegant, 3Blue1Brown aesthetic
- The wall/constraint metaphor should be clear

## Preview of Part 3

This section visually introduces the three components that Part 3 will explain in detail:
1. **Tests (walls)** - detailed in Part 3.1
2. **Prompts (specification)** - detailed in Part 3.2
3. **Grounding (not yet shown)** - introduced in Part 3.3

## Transition

This concludes Part 2. Fade or cut to Part 3 (The Mold Has Three Parts), which will elaborate on this framework with detailed explanations of each component.

## End State

The final frame should show:
- Glowing prompt (top)
- Glowing test walls (forming container)
- Code filled in container (not glowing)
- Clear visual hierarchy of value

This image will be referenced again throughout Part 3.
