# Section 3.5: Bug Discovered

**Tool:** Hybrid (Video + Remotion overlay)
**Duration:** ~15 seconds
**Timestamp:** 11:30 - 11:45

## Visual Description

A bug is discovered in the generated code. Red alert indicators appear on a piece of code, and the word "BUG" materializes. This creates the problem that Section 3.6 will solve. No terminal commands are shown in this section -- the terminal (`pdd bug user_parser`) belongs to the next section (06).

## Option A: Video Primary (Preferred)

### Video Base
- Close-up of code on screen
- Could use screen recording or generated footage
- Focus on a function with an edge case bug

### Veo Prompt (if generating)
```
Close-up of computer screen showing code.

SUBJECT:
- IDE or code editor interface
- Python or TypeScript code visible
- Function handling user input
- Subtle error in the code (variable name, logic)

ACTION:
- Code is static initially
- A line highlights (cursor or selection)
- Problem becomes visible

ENVIRONMENT:
- Dark theme IDE
- Soft monitor glow
- Developer workspace feel

NO PEOPLE
NO TEXT OVERLAY (Remotion will add)
DURATION: 12 seconds
```

### Remotion Overlay
- Red highlight circle around bug location
- "BUG" label appears with alert animation

## Option B: Full Remotion

### Animation Elements

1. **Code Display**
   - Stylized code block in center
   - Monospace font, syntax highlighted
   - Function with a visible bug

2. **Bug Highlight**
   - Red pulsing circle around bug location
   - Scan line effect moving down code
   - "BUG" label materializes

### Sample Bug Code

```python
def parse_user_id(input_str):
    if not input_str:
        return None
    # BUG: Doesn't handle whitespace-only input
    return input_str.strip()
```

The bug: `"   "` (whitespace only) passes the `if not input_str` check but returns empty string after strip.

### Animation Sequence

1. **Frame 0-90 (0-3s):** Code appears
   - Code block fades in
   - Clean, readable display
   - Nothing highlighted yet

2. **Frame 90-180 (3-6s):** Scan/analysis effect
   - Scan line moves down code
   - Analyzing feel
   - Building tension

3. **Frame 180-270 (6-9s):** Bug highlight
   - Red circle appears around bug line
   - Pulsing animation
   - "BUG" label fades in above

4. **Frame 270-450 (9-15s):** Hold
   - Bug clearly highlighted
   - Problem established
   - Ready for solution

### Code Structure (Remotion)

```typescript
const BugDiscovered: React.FC = () => {
  const frame = useCurrentFrame();

  // Scan line position
  const scanY = interpolate(
    frame,
    [90, 180],
    [0, 300],
    { extrapolateRight: 'clamp' }
  );

  // Bug highlight visibility
  const bugHighlight = interpolate(
    frame,
    [180, 210],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Bug label pulse
  const bugPulse = Math.sin(frame * 0.15) * 0.1 + 1;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <CodeBlock code={buggyCode} />
      {frame > 90 && frame < 180 && <ScanLine y={scanY} />}
      <BugHighlight
        opacity={bugHighlight}
        scale={bugPulse}
        line={4}
      />
      <BugLabel opacity={bugHighlight} scale={bugPulse} />
    </AbsoluteFill>
  );
};
```

### Hybrid Composition

```typescript
const BugDiscoveredHybrid: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <Video src="code_screen.mp4" />

      {/* Remotion overlays */}
      <Sequence from={180}>
        <BugHighlightOverlay
          position={{ x: 420, y: 280 }}
          color="#D94A4A"
        />
      </Sequence>

      <Sequence from={210}>
        <AnimatedLabel
          text="BUG"
          color="#D94A4A"
          position={{ x: 420, y: 220 }}
        />
      </Sequence>
    </AbsoluteFill>
  );
};
```

### Color Palette

- Bug highlight: Red (#D94A4A)
- Code background: Dark (#1E1E2E)
- Code text: Syntax highlighted

### Easing

- Scan line: Linear
- Bug highlight: `easeOutBack` (slight overshoot)
- Label appearance: `easeOutCubic`
- Pulse: `easeInOutSine`

## Narration Sync

> "Now here's where it gets interesting. When you find a bug..."

The bug highlight appears as "bug" is spoken, creating visual emphasis.

## Audio Notes

- Subtle "scan" sound during analysis
- Alert/warning tone when bug is found

## Visual Style Notes

- Red is used sparingly but effectively
- This is a PROBLEM that needs solving
- Build tension for the "add a wall" solution

## Transition

Cuts to Section 3.6 where instead of patching, a new test wall is added.
