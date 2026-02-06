# Section 4.7: Short Prompt with Many Tests

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 17:30 - 17:45

## Visual Description

A minimal 10-line prompt file (`parser_v2.prompt`) appears, surrounded by dozens of amber test walls. In the corner, a terminal shows `pdd test parser` with "47 tests passed". The contrast with Section 4.6 is stark: same functionality, fraction of the prompt.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Prompt centered, walls surrounding it

### Animation Elements

1. **Prompt File Display**
   - File: `parser_v2.prompt`
   - Only ~10 lines of high-level intent
   - Blue (#4A90D9) header/accent
   - Clean, minimal content

2. **Test Walls (Many)**
   - 25+ amber walls surrounding prompt
   - Dense arrangement, forming a "mold"
   - Active, glowing appearance

3. **Terminal Snippet**
   - Bottom-right corner
   - Shows: `$ pdd test parser`
   - Output: "47 tests passed" with checkmark

4. **Line Count Indicator**
   - "10 lines" badge visible
   - Contrast with previous 50 lines

### Visual Design

```
┌────────────────────────────────────┐
│                                    │
│  ┌──┐ ┌──┐ ┌──┐ ┌──┐ ┌──┐ ┌──┐    │
│  │  │ │  │ │  │ │  │ │  │ │  │    │
│  └──┘ └──┘ └──┘ └──┘ └──┘ └──┘    │
│  ┌──┐ ┌─ parser_v2.prompt ─┐ ┌──┐ │
│  │  │ │                    │ │  │ │
│  └──┘ │ # User ID Parser   │ └──┘ │
│  ┌──┐ │ Parse user IDs.    │ ┌──┐ │
│  │  │ │ Return None on     │ │  │ │
│  └──┘ │ failure.      [10L]│ └──┘ │
│  ┌──┐ └────────────────────┘ ┌──┐ │
│  │  │                        │  │ │
│  └──┘ ┌──┐ ┌──┐ ┌──┐ ┌──┐   └──┘ │
│       │  │ │  │ │  │ │  │        │
│       └──┘ └──┘ └──┘ └──┘        │
│                                   │
│           ┌─────────────────────┐ │
│           │$ pdd test parser    │ │
│           │47 tests passed ✓    │ │
│           └─────────────────────┘ │
└────────────────────────────────────┘
        ^ walls surround prompt
```

### Sample Prompt Content

```markdown
# User ID Parser

Parse and validate user IDs from input.
Return None for any invalid input.
Handle all edge cases gracefully.
Never throw exceptions.

See tests for exact behavior.
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Prompt file appears
   - Small, minimal prompt fades in
   - Centered in frame
   - Clean, simple appearance

2. **Frame 90-210 (3-7s):** Test walls materialize
   - Walls appear one by one around prompt
   - Satisfying "click" animation for each
   - Building up the constraint boundary

3. **Frame 210-330 (7-11s):** Terminal appears
   - Terminal snippet fades in bottom-right
   - `pdd test parser` command visible
   - "47 tests passed ✓" output

4. **Frame 330-450 (11-15s):** Hold
   - All elements visible
   - Walls gently pulse
   - Strong contrast with 4.6 established

### Code Structure (Remotion)

```typescript
const ShortPromptTests: React.FC = () => {
  const frame = useCurrentFrame();

  // Prompt opacity
  const promptOpacity = interpolate(
    frame,
    [0, 90],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Number of walls visible (staggered appearance)
  const wallCount = Math.min(
    30,
    Math.floor(interpolate(
      frame,
      [90, 210],
      [0, 30],
      { extrapolateRight: 'clamp' }
    ))
  );

  // Terminal opacity
  const terminalOpacity = interpolate(
    frame,
    [210, 270],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Wall pulse effect
  const wallPulse = frame > 210 ?
    1 + Math.sin(frame * 0.08) * 0.05 : 1;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Small prompt file */}
      <SmallPromptFile
        filename="parser_v2.prompt"
        content={shortPromptContent}
        lineCount={10}
        opacity={promptOpacity}
      />

      {/* Many test walls surrounding prompt */}
      <SurroundingWalls
        count={wallCount}
        pulse={wallPulse}
      />

      {/* Terminal snippet */}
      <TerminalSnippet
        command="pdd test parser"
        output="47 tests passed ✓"
        opacity={terminalOpacity}
      />
    </AbsoluteFill>
  );
};
```

### Small Prompt File Component

```typescript
const SmallPromptFile: React.FC<{
  filename: string;
  content: string;
  lineCount: number;
  opacity: number;
}> = ({ filename, content, lineCount, opacity }) => {
  return (
    <div style={{
      position: 'absolute',
      left: '50%',
      top: '50%',
      transform: 'translate(-50%, -50%)',
      width: 500,
      opacity,
    }}>
      {/* File header */}
      <div style={{
        backgroundColor: '#4A90D9',
        padding: '10px 16px',
        borderTopLeftRadius: 8,
        borderTopRightRadius: 8,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'space-between',
      }}>
        <span style={{
          color: 'white',
          fontFamily: 'monospace',
          fontSize: 16,
        }}>
          {filename}
        </span>
        <span style={{
          color: 'rgba(255, 255, 255, 0.7)',
          fontSize: 12,
        }}>
          {lineCount} lines
        </span>
      </div>

      {/* File content */}
      <div style={{
        backgroundColor: '#1E1E2E',
        padding: 16,
        borderBottomLeftRadius: 8,
        borderBottomRightRadius: 8,
      }}>
        {content.split('\n').map((line, i) => (
          <div key={i} style={{
            fontFamily: 'monospace',
            fontSize: 14,
            color: line.startsWith('#') ? '#4A90D9' :
                   'rgba(255, 255, 255, 0.8)',
            marginBottom: 4,
          }}>
            {line}
          </div>
        ))}
      </div>
    </div>
  );
};
```

### Surrounding Walls Component

```typescript
const SurroundingWalls: React.FC<{
  count: number;
  pulse: number;
}> = ({ count, pulse }) => {
  // Generate wall positions in a ring around center
  const walls = [];
  const centerX = 960;
  const centerY = 540;
  const innerRadius = 300;
  const outerRadius = 480;

  for (let i = 0; i < count; i++) {
    const angle = (i / 30) * Math.PI * 2;
    const radius = innerRadius + (i % 3) * 60;
    walls.push({
      x: centerX + Math.cos(angle) * radius - 20,
      y: centerY + Math.sin(angle) * radius - 30,
      delay: i * 4, // Stagger animation
    });
  }

  return (
    <>
      {walls.map((wall, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            left: wall.x,
            top: wall.y,
            width: 40,
            height: 60,
            backgroundColor: '#D9944A',
            borderRadius: 4,
            transform: `scale(${pulse})`,
            boxShadow: '0 0 20px rgba(217, 148, 74, 0.5)',
          }}
        />
      ))}
    </>
  );
};
```

### Terminal Snippet Component

```typescript
const TerminalSnippet: React.FC<{
  command: string;
  output: string;
  opacity: number;
}> = ({ command, output, opacity }) => {
  return (
    <div style={{
      position: 'absolute',
      right: 80,
      bottom: 80,
      backgroundColor: 'rgba(30, 30, 46, 0.95)',
      borderRadius: 8,
      padding: 16,
      opacity,
      border: '1px solid rgba(255, 255, 255, 0.1)',
    }}>
      <div style={{
        fontFamily: 'monospace',
        fontSize: 14,
        color: 'rgba(255, 255, 255, 0.7)',
        marginBottom: 8,
      }}>
        $ {command}
      </div>
      <div style={{
        fontFamily: 'monospace',
        fontSize: 14,
        color: '#5AAA6E',
        display: 'flex',
        alignItems: 'center',
        gap: 8,
      }}>
        {output}
      </div>
    </div>
  );
};
```

### Easing

- Prompt fade-in: `easeOutCubic`
- Wall appearance: Staggered with `easeOutBack` (slight overshoot)
- Terminal fade-in: `easeOutCubic`
- Wall pulse: `easeInOutSine`

## Narration Sync

> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

The minimal prompt surrounded by many walls visually demonstrates that tests handle the constraints.

## Audio Notes

- Soft appearance sound for prompt
- Satisfying "click" for each wall materializing
- Success chime when terminal shows passing tests
- Rich, layered soundscape

## Visual Style Notes

- Small prompt should feel light and minimal
- Many walls create visual "weight" around it
- Terminal confirmation adds satisfaction
- Strong contrast with previous scene

## Transition

Cuts to Section 4.8 for the final split comparison and message.
