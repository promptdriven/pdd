# Section 6.3: Developer Regenerates Instead of Patching

**Tool:** Hybrid (Video + Remotion overlay)
**Duration:** ~15 seconds
**Timestamp:** 20:40 - 20:55

## Visual Description

Code with a bug is visible. A developer considers it. Instead of opening the file to patch, they add a test and hit "regenerate." A terminal overlay shows the PDD workflow: `pdd bug` -> `pdd fix` -> checkmark. The parallel to the sock is unmistakable -- discard and replace, don't patch.

## Video Base

### Veo 3.1 Prompt

```
A developer sitting at a desk with a monitor visible. They look at the screen, pause briefly in thought, then confidently type a few keystrokes. Their expression shifts from concern to satisfaction.

SUBJECT:
- Developer, 25-40, any gender
- Modern workspace with single monitor
- Keyboard and mouse visible
- Expression progression: puzzled -> thoughtful -> decisive -> satisfied

ACTION:
- Looking at screen with mild concern (2 seconds)
- Brief pause, thinking (1 second)
- Decisive typing -- short, purposeful keystrokes (5 seconds)
- Lean back slightly, satisfied nod (3 seconds)
- Optional: brief smile

ENVIRONMENT:
- Modern home office or desk
- Dark-ish ambient with monitor glow
- Clean, minimal
- Similar aesthetic to Cold Open developer

CAMERA:
- Medium shot, slight over-the-shoulder angle
- Monitor partially visible
- Focus on developer's expression and hands

MOOD: Confident. This person KNOWS the right thing to do. No hesitation, no stress.

DURATION: 15 seconds
NO TEXT OVERLAY (Remotion will add terminal)
```

## Remotion Overlay Specifications

### Canvas
- Resolution: 1920x1080
- Overlay on video base
- Terminal overlay positioned as if on the developer's monitor

### Overlay Elements

1. **Terminal Window**
   - Positioned to align with the monitor in the video
   - Dark terminal background (#1E1E2E)
   - Rounded corners, subtle border
   - Size: ~500x300px

2. **Bug Display (Initial)**
   - Code snippet with a visible bug (red highlight)
   - 3-4 lines of Python-like pseudocode
   - Bug line marked with red squiggly or highlight

3. **PDD Command Sequence**
   - `$ pdd bug parser` -- typed, amber text
   - Output: `Bug identified: off-by-one in line 23`
   - `$ pdd fix parser` -- typed, blue text
   - Progress indicator: `Regenerating...`
   - Output: `Generated parser.py (247 lines)`
   - `$ pdd test parser` -- typed, green text
   - Output: `47 tests passed` with green checkmark

4. **Success Indicator**
   - Large green checkmark that pulses once
   - Appears at end of command sequence

### Visual Design

```
┌──────────────────────────────────────────────────────────┐
│                                                          │
│         ┌──── Developer Video ────────────┐              │
│         │                                 │              │
│         │    Developer at desk            │              │
│         │                                 │              │
│         │   ┌─── Terminal Overlay ──────┐ │              │
│         │   │ $ pdd bug parser          │ │              │
│         │   │ Bug: off-by-one in ln 23  │ │              │
│         │   │                           │ │              │
│         │   │ $ pdd fix parser          │ │              │
│         │   │ Regenerating...           │ │              │
│         │   │ Generated parser.py       │ │              │
│         │   │                           │ │              │
│         │   │ $ pdd test parser         │ │              │
│         │   │ 47 tests passed ✓         │ │              │
│         │   └───────────────────────────┘ │              │
│         │                                 │              │
│         └─────────────────────────────────┘              │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Bug visible
   - Video: Developer looking at screen with concern
   - Overlay: Terminal shows code with red-highlighted bug
   - Establishes the problem

2. **Frame 60-90 (2-3s):** Decision moment
   - Video: Developer pauses, thinks
   - Overlay: Terminal unchanged
   - Key moment: the developer does NOT open the file to edit

3. **Frame 90-150 (3-5s):** `pdd bug`
   - Video: Developer starts typing
   - Overlay: `$ pdd bug parser` types out character-by-character
   - Output appears: bug identification

4. **Frame 150-240 (5-8s):** `pdd fix`
   - Video: Developer continues typing
   - Overlay: `$ pdd fix parser` types out
   - "Regenerating..." with animated dots
   - "Generated parser.py (247 lines)" appears

5. **Frame 240-330 (8-11s):** `pdd test`
   - Video: Developer types final command
   - Overlay: `$ pdd test parser` types out
   - "47 tests passed" with green checkmark

6. **Frame 330-450 (11-15s):** Success hold
   - Video: Developer leans back, satisfied
   - Overlay: Large green checkmark pulses once
   - Terminal content held steady
   - The ease of the process is the point

### Code Structure (Remotion)

```typescript
const DeveloperRegenerates: React.FC = () => {
  const frame = useCurrentFrame();

  // Terminal visibility
  const terminalOpacity = interpolate(
    frame,
    [0, 30],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Command typing progress
  const bugCommandProgress = interpolate(
    frame,
    [90, 130],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const fixCommandProgress = interpolate(
    frame,
    [150, 190],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const testCommandProgress = interpolate(
    frame,
    [240, 280],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Bug output
  const bugOutputOpacity = interpolate(
    frame,
    [135, 150],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Fix output
  const regeneratingOpacity = interpolate(
    frame,
    [195, 210],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const generatedOpacity = interpolate(
    frame,
    [215, 235],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Test result
  const testResultOpacity = interpolate(
    frame,
    [290, 310],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Success checkmark scale (pop effect)
  const checkScale = interpolate(
    frame,
    [310, 340, 360],
    [0, 1.2, 1.0],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <Video src="developer_regenerates.mp4" />

      {/* Terminal overlay */}
      <div style={{
        position: 'absolute',
        right: 120,
        top: 180,
        width: 500,
        opacity: terminalOpacity,
        backgroundColor: 'rgba(30, 30, 46, 0.92)',
        borderRadius: 12,
        border: '1px solid rgba(255, 255, 255, 0.15)',
        padding: 20,
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: 14,
        backdropFilter: 'blur(8px)',
      }}>
        {/* Terminal title bar */}
        <TerminalTitleBar title="terminal" />

        {/* Bug command */}
        <TerminalLine
          prompt="$"
          command="pdd bug parser"
          progress={bugCommandProgress}
          color="#D9944A"
        />
        {bugOutputOpacity > 0 && (
          <TerminalOutput
            text="Bug identified: off-by-one in line 23"
            opacity={bugOutputOpacity}
            color="rgba(255, 100, 100, 0.8)"
          />
        )}

        {/* Fix command */}
        {frame > 150 && (
          <TerminalLine
            prompt="$"
            command="pdd fix parser"
            progress={fixCommandProgress}
            color="#4A90D9"
          />
        )}
        {regeneratingOpacity > 0 && (
          <TerminalOutput
            text="Regenerating..."
            opacity={regeneratingOpacity}
            color="rgba(255, 255, 255, 0.5)"
            animated={true}
          />
        )}
        {generatedOpacity > 0 && (
          <TerminalOutput
            text="Generated parser.py (247 lines)"
            opacity={generatedOpacity}
            color="rgba(255, 255, 255, 0.7)"
          />
        )}

        {/* Test command */}
        {frame > 240 && (
          <TerminalLine
            prompt="$"
            command="pdd test parser"
            progress={testCommandProgress}
            color="#5AAA6E"
          />
        )}
        {testResultOpacity > 0 && (
          <div style={{ opacity: testResultOpacity }}>
            <span style={{ color: '#5AAA6E' }}>47 tests passed </span>
            <span style={{
              color: '#5AAA6E',
              fontSize: 18,
              transform: `scale(${checkScale})`,
              display: 'inline-block',
            }}>
              ✓
            </span>
          </div>
        )}
      </div>
    </AbsoluteFill>
  );
};
```

### Easing

- Terminal fade-in: `easeOutCubic`
- Command typing: Linear (typewriter feel)
- Output appearance: `easeOutQuad`
- Checkmark pop: `easeOutBack` (satisfying overshoot)

## Narration Sync

> "Code just got that cheap."

This is a SHORT, punchy narration. "Code" lands as the `pdd bug` command runs. "Just got that cheap" hits as the checkmark appears. The brevity of the narration mirrors the brevity of the fix process -- this took seconds, not hours.

## Audio Notes

- Keyboard clicks synced to typing in the overlay (subtle, not literal)
- "Regenerating..." accompanied by a brief digital processing sound
- Success checkmark: Clean, bright chime
- Harmonious resolution when all tests pass (per script sound design notes)
- The ease should be AUDIBLE -- this sounds effortless

## Visual Style Notes

- The terminal overlay should look like it belongs on the developer's screen
- Semi-transparent background with backdrop blur creates the illusion
- PDD commands use the project's color scheme: bug (amber), fix (blue), test (green)
- The developer's body language tells the story: concern -> confidence -> satisfaction
- This parallels the sock discard -- same instinct, applied to code
- The three-command sequence (`bug -> fix -> test`) should feel like a natural workflow

## PDD Commands Shown

| Command | Color | Meaning |
|---------|-------|---------|
| `pdd bug parser` | Amber (#D9944A) | Identify the problem |
| `pdd fix parser` | Blue (#4A90D9) | Regenerate the code |
| `pdd test parser` | Green (#5AAA6E) | Verify the fix |

## Transition

Cuts to Section 6.4, where the three PDD components crystallize into a triangle diagram.
