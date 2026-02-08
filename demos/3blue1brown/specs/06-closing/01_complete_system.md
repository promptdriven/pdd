# Section 6.1: Complete System Pull-Back

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 20:15 - 20:25

## Visual Description

Pull back to show a complete system. Multiple modules are visible, each with a prompt, tests, and generated code. The prompts and tests glow steadily with their signature colors. The code is present but not highlighted -- it is output, not the source of value. This is the "big picture" view that frames the closing argument.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)

### Animation Elements

1. **Multiple Module Blocks (4-5 modules)**
   - Each module is a self-contained unit arranged in a grid or staggered layout
   - Module names: `auth.prompt`, `parser.prompt`, `api.prompt`, `db.prompt`, `utils.prompt`
   - Each module contains three visible layers: prompt file (blue), test files (amber), generated code (gray)

2. **Prompt Files (Glowing)**
   - Color: Blue (#4A90D9) with steady outer glow
   - Box shadow: `0 0 20px rgba(74, 144, 217, 0.6)`
   - Labeled with `.prompt` extension
   - Visually prominent -- the "source of truth"

3. **Test Files (Glowing)**
   - Color: Amber (#D9944A) with steady outer glow
   - Box shadow: `0 0 20px rgba(217, 148, 74, 0.6)`
   - Labeled with `test_` prefix
   - Visually prominent alongside prompts

4. **Generated Code (Dim, No Glow)**
   - Color: Neutral gray (#A0A0A0) at reduced opacity (0.4-0.5)
   - No glow, no box shadow
   - Present but visually receding -- "just output"
   - Labeled with `.py` extension

5. **Connection Lines**
   - Faint dashed lines connecting prompt -> code within each module
   - Show derivation relationship
   - Very subtle, not distracting

### Visual Design

```
┌──────────────────────────────────────────────────────────────┐
│                                                              │
│   ┌─ auth ─────────┐    ┌─ parser ──────────┐               │
│   │ ╔═auth.prompt═╗ │    │ ╔═parser.prompt═╗  │              │
│   │ ║  ✦ GLOWS ✦  ║ │    │ ║  ✦ GLOWS ✦   ║  │              │
│   │ ╚═════════════╝ │    │ ╚══════════════╝  │              │
│   │ ┌test_auth─────┐│    │ ┌test_parser────┐ │              │
│   │ │ ✦ GLOWS ✦    ││    │ │ ✦ GLOWS ✦     │ │              │
│   │ └──────────────┘│    │ └───────────────┘ │              │
│   │ ┌auth.py───────┐│    │ ┌parser.py──────┐ │              │
│   │ │  (dim gray)  ││    │ │  (dim gray)   │ │              │
│   │ └──────────────┘│    │ └───────────────┘ │              │
│   └─────────────────┘    └──────────────────┘               │
│                                                              │
│   ┌─ api ──────────┐    ┌─ db ─────────────┐               │
│   │ ╔═api.prompt══╗ │    │ ╔═db.prompt════╗  │              │
│   │ ║  ✦ GLOWS ✦  ║ │    │ ║  ✦ GLOWS ✦   ║  │              │
│   │ ╚═════════════╝ │    │ ╚══════════════╝  │              │
│   │ ┌test_api─────┐ │    │ ┌test_db────────┐ │              │
│   │ │ ✦ GLOWS ✦   │ │    │ │ ✦ GLOWS ✦     │ │              │
│   │ └─────────────┘ │    │ └───────────────┘ │              │
│   │ ┌api.py───────┐ │    │ ┌db.py──────────┐ │              │
│   │ │  (dim gray) │ │    │ │  (dim gray)   │ │              │
│   │ └─────────────┘ │    │ └───────────────┘ │              │
│   └─────────────────┘    └──────────────────┘               │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Camera pulls back
   - View zooms out from a single module to the full grid
   - Scale interpolation: `1.8 -> 1.0`
   - Modules appear to be "revealed" rather than animated in

2. **Frame 60-150 (2-5s):** Glows activate sequentially
   - Prompts glow first (blue pulse across all modules, left-to-right)
   - Tests glow next (amber pulse, same sweep)
   - Each glow activates in ~0.3s stagger per module

3. **Frame 150-240 (5-8s):** Code dims
   - All `.py` code files simultaneously dim to 40% opacity
   - Subtle: the viewer's attention is drawn to what glows
   - No animation on code -- it just recedes

4. **Frame 240-300 (8-10s):** Hold full system
   - Everything steady
   - Prompts and tests glow continuously
   - Code visible but unremarkable
   - System feels complete and stable

### Code Structure (Remotion)

```typescript
const CompleteSystem: React.FC = () => {
  const frame = useCurrentFrame();

  // Camera pull-back (zoom out)
  const scale = interpolate(
    frame,
    [0, 60],
    [1.8, 1.0],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Glow activation for prompts (staggered per module)
  const promptGlow = (moduleIndex: number) => interpolate(
    frame,
    [60 + moduleIndex * 10, 90 + moduleIndex * 10],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Glow activation for tests (staggered, after prompts)
  const testGlow = (moduleIndex: number) => interpolate(
    frame,
    [100 + moduleIndex * 10, 130 + moduleIndex * 10],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Code dim
  const codeDim = interpolate(
    frame,
    [150, 200],
    [0.8, 0.4],
    { extrapolateRight: 'clamp' }
  );

  const modules = [
    { name: 'auth', x: 200, y: 150 },
    { name: 'parser', x: 600, y: 150 },
    { name: 'api', x: 200, y: 500 },
    { name: 'db', x: 600, y: 500 },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <div style={{
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
        width: '100%',
        height: '100%',
      }}>
        {modules.map((mod, i) => (
          <ModuleBlock
            key={mod.name}
            name={mod.name}
            position={{ x: mod.x, y: mod.y }}
            promptGlow={promptGlow(i)}
            testGlow={testGlow(i)}
            codeOpacity={codeDim}
          />
        ))}

        {/* Subtle connection lines between modules */}
        <ModuleConnections modules={modules} opacity={0.15} />
      </div>
    </AbsoluteFill>
  );
};
```

### Module Block Component

```typescript
const ModuleBlock: React.FC<{
  name: string;
  position: { x: number; y: number };
  promptGlow: number;
  testGlow: number;
  codeOpacity: number;
}> = ({ name, position, promptGlow, testGlow, codeOpacity }) => {
  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      width: 320,
    }}>
      {/* Module label */}
      <div style={{
        fontSize: 14,
        color: 'rgba(255, 255, 255, 0.5)',
        marginBottom: 8,
        fontFamily: 'monospace',
      }}>
        {name}/
      </div>

      {/* Prompt file - GLOWS */}
      <div style={{
        backgroundColor: 'rgba(74, 144, 217, 0.15)',
        border: '1px solid #4A90D9',
        borderRadius: 6,
        padding: '8px 12px',
        marginBottom: 6,
        boxShadow: `0 0 ${20 * promptGlow}px rgba(74, 144, 217, ${0.6 * promptGlow})`,
        fontFamily: 'monospace',
        fontSize: 13,
        color: '#4A90D9',
      }}>
        {name}.prompt
      </div>

      {/* Test file - GLOWS */}
      <div style={{
        backgroundColor: 'rgba(217, 148, 74, 0.15)',
        border: '1px solid #D9944A',
        borderRadius: 6,
        padding: '8px 12px',
        marginBottom: 6,
        boxShadow: `0 0 ${20 * testGlow}px rgba(217, 148, 74, ${0.6 * testGlow})`,
        fontFamily: 'monospace',
        fontSize: 13,
        color: '#D9944A',
      }}>
        test_{name}.py
      </div>

      {/* Generated code - NO GLOW, dim */}
      <div style={{
        backgroundColor: 'rgba(160, 160, 160, 0.08)',
        border: '1px solid rgba(160, 160, 160, 0.2)',
        borderRadius: 6,
        padding: '8px 12px',
        opacity: codeOpacity,
        fontFamily: 'monospace',
        fontSize: 13,
        color: 'rgba(160, 160, 160, 0.6)',
      }}>
        {name}.py
      </div>
    </div>
  );
};
```

### Easing

- Camera pull-back: `easeOutCubic` (smooth deceleration)
- Glow activation: `easeOutQuad` (natural ramp-up)
- Code dim: `easeOutQuad` (gentle fade)

## Narration Sync

> "So here's the mental shift."

The camera pull-back begins on "So" and completes by "mental shift." The glows activate during "mental shift," drawing the eye to what matters. The held frame allows the statement to land.

## Audio Notes

- Subtle ambient hum as the system is revealed
- Soft harmonic tone as glows activate
- Silence/calm during hold -- let the visual speak
- This is a moment of clarity, not spectacle

## Visual Style Notes

- The pull-back should feel like stepping back to see the big picture
- Glow vs. no-glow is the ENTIRE message of this frame
- Do not over-animate -- simplicity reinforces the point
- The grid layout should feel organized and intentional
- 3Blue1Brown aesthetic: clean, mathematical, deliberate

## Transition

The held system view transitions into Section 6.2, where the sock metaphor returns for its final callback.
