# Section 3.11: Prompt Text Flows

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 13:25 - 13:40

## Visual Description

Text flows into the mold like injection material: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." A file briefly becomes visible: `user_parser.prompt`. This shows the prompt as the input specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Mold cross-section with nozzle prominent

### Animation Elements

1. **Prompt Text**
   - Three lines of specification text
   - Flows downward from nozzle
   - Transforms from text to "liquid" as it enters mold

2. **File Reference**
   - `user_parser.prompt` visible briefly
   - Document icon with blue glow
   - Shows source of the specification

3. **Flow Animation**
   - Text starts readable at top
   - Becomes fluid as it enters nozzle
   - Fills mold cavity below

4. **Text Content**
   - "Parse user IDs from untrusted input."
   - "Return None on failure, never throw."
   - "Handle unicode."

### Animation Sequence

1. **Frame 0-90 (0-3s):** File appears
   - `user_parser.prompt` document fades in
   - Blue glow around document
   - Position: above nozzle

2. **Frame 90-180 (3-6s):** First line flows
   - "Parse user IDs from untrusted input."
   - Text streams downward
   - Enters nozzle, becomes fluid

3. **Frame 180-270 (6-9s):** Second line flows
   - "Return None on failure, never throw."
   - Same streaming effect
   - Adds to flow

4. **Frame 270-360 (9-12s):** Third line flows
   - "Handle unicode."
   - Final specification text
   - Flow continues into mold

5. **Frame 360-450 (12-15s):** Transformation complete
   - All text has become fluid
   - Filling the constrained cavity
   - Prompt → Code transformation

### Visual Design: Text to Fluid

```
user_parser.prompt
┌─────────────────────────┐
│ Parse user IDs from     │
│ untrusted input.        │◄── Readable text
│                         │
│ Return None on failure, │
│ never throw.            │
│                         │
│ Handle unicode.         │
└─────────────────────────┘
           │
           ▼
     ═══════════════
          ╲   ╱      ◄── Text transforms
           ╲ ╱           to fluid
            │
    ┌───────┴───────┐
    │    NOZZLE     │
    └───────┬───────┘
            │
      ▓▓▓▓▓▓▓▓▓▓▓▓    ◄── Fluid fills
      ▓▓▓▓▓▓▓▓▓▓▓▓        constrained
      ▓▓▓▓▓▓▓▓▓▓▓▓        cavity
```

### Code Structure (Remotion)

```typescript
const PromptTextFlows: React.FC = () => {
  const frame = useCurrentFrame();

  const promptLines = [
    { text: "Parse user IDs from untrusted input.", start: 90 },
    { text: "Return None on failure, never throw.", start: 180 },
    { text: "Handle unicode.", start: 270 },
  ];

  // Document visibility
  const docOpacity = interpolate(
    frame,
    [0, 60, 360, 420],
    [0, 1, 1, 0.3],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <MoldCrossSection wallOpacity={0.4} />
      <NozzleHighlight glowIntensity={1} color="#4A90D9" />

      {/* Prompt document */}
      <PromptDocument
        filename="user_parser.prompt"
        opacity={docOpacity}
        position={{ x: 960, y: 120 }}
      />

      {/* Flowing text lines */}
      {promptLines.map((line, i) => (
        <FlowingText
          key={i}
          text={line.text}
          startFrame={line.start}
          currentFrame={frame}
          nozzleY={280}
        />
      ))}

      {/* Fluid accumulation in mold */}
      <FluidInMold
        fillLevel={interpolate(frame, [90, 400], [0, 1])}
        color="#8A9CAF"
      />
    </AbsoluteFill>
  );
};
```

### Flowing Text Effect

```typescript
const FlowingText: React.FC<{
  text: string;
  startFrame: number;
  currentFrame: number;
  nozzleY: number;
}> = ({ text, startFrame, currentFrame, nozzleY }) => {
  const elapsed = currentFrame - startFrame;
  if (elapsed < 0) return null;

  // Text position (moves down)
  const y = interpolate(
    elapsed,
    [0, 60],
    [80, nozzleY],
    { extrapolateRight: 'clamp' }
  );

  // Text opacity (fades as it enters nozzle)
  const opacity = interpolate(
    elapsed,
    [0, 30, 60, 90],
    [0, 1, 1, 0],
    { extrapolateRight: 'clamp' }
  );

  // Text scale (shrinks into nozzle)
  const scale = interpolate(
    elapsed,
    [40, 70],
    [1, 0.3],
    { extrapolateRight: 'clamp' }
  );

  // Text blur (becomes fluid)
  const blur = interpolate(
    elapsed,
    [50, 70],
    [0, 5],
    { extrapolateRight: 'clamp' }
  );

  return (
    <div style={{
      position: 'absolute',
      left: '50%',
      top: y,
      transform: `translateX(-50%) scale(${scale})`,
      opacity,
      filter: `blur(${blur}px)`,
      color: '#4A90D9',
      fontSize: 20,
      fontFamily: 'JetBrains Mono',
      whiteSpace: 'nowrap',
    }}>
      {text}
    </div>
  );
};
```

### Prompt Document Component

```typescript
const PromptDocument: React.FC<{
  filename: string;
  opacity: number;
  position: Point;
}> = ({ filename, opacity, position }) => {
  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      transform: 'translateX(-50%)',
      opacity,
    }}>
      {/* Document icon */}
      <div style={{
        width: 180,
        background: 'rgba(74, 144, 217, 0.1)',
        border: '2px solid #4A90D9',
        borderRadius: 8,
        padding: 12,
        boxShadow: '0 0 20px rgba(74, 144, 217, 0.3)',
      }}>
        <div style={{
          fontSize: 12,
          color: '#4A90D9',
          fontFamily: 'JetBrains Mono',
          marginBottom: 8,
        }}>
          {filename}
        </div>
        <div style={{
          fontSize: 10,
          color: '#888',
          lineHeight: 1.4,
        }}>
          Parse user IDs...<br />
          Return None...<br />
          Handle unicode.
        </div>
      </div>
    </div>
  );
};
```

### Easing

- Document fade: `easeOutCubic`
- Text descent: `easeInQuad` (accelerating into nozzle)
- Text blur: `easeInQuad`
- Fluid fill: Physics-based

## Narration Sync

> "The prompt doesn't define the walls—tests do that. The prompt defines what you're asking for and why."

The prompt text flows during this narration, making clear the distinction between prompt (what) and tests (constraints).

## Audio Notes

- Soft "stream" sound as text flows
- Paper/document sound when file appears
- Transformation sound as text becomes fluid
- Satisfying fill sounds

## Visual Style Notes

- Text is readable before transformation
- The transformation is smooth, not jarring
- Blue color connects to nozzle/prompt theme
- The file reference (`user_parser.prompt`) is important context
- Shows that prompts are files, not magic

## Transition

Continues into Section 3.12 showing the same prompt generating different valid outputs.
