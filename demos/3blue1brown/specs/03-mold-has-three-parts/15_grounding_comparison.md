# Section 3.15: Grounding Comparison (OOP vs Functional)

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 14:30 - 14:55

## Visual Description

Same prompt, same tests. But two different grounding contexts produce different code styles. Path A: Grounding from OOP codebase → generates classes with methods. Path B: Grounding from functional codebase → generates pure functions with composition.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Split screen with shared source

### Animation Elements

1. **Shared Source (Top Center)**
   - Same prompt (blue)
   - Same tests (amber walls)
   - "Same specification" label

2. **Path A: OOP (Left)**
   - Grounding indicator: "OOP Codebase"
   - Generated code with classes
   - Green-tinted flow

3. **Path B: Functional (Right)**
   - Grounding indicator: "Functional Codebase"
   - Generated code with pure functions
   - Green-tinted flow (same color, different output)

4. **Both Pass Tests**
   - Both sides show green checkmarks
   - Same behavior, different implementation style

### Code Examples

**OOP Output:**
```python
class UserParser:
    def __init__(self):
        self._validators = [...]

    def parse(self, input_str: str) -> Optional[str]:
        if not input_str:
            return None
        cleaned = self._sanitize(input_str)
        return cleaned if self._validate(cleaned) else None

    def _sanitize(self, value: str) -> str:
        return value.strip()

    def _validate(self, value: str) -> bool:
        return bool(value) and value.isalnum()
```

**Functional Output:**
```python
def parse_user_id(input_str: str) -> Optional[str]:
    return pipe(
        input_str,
        sanitize,
        validate,
        lambda x: x if x else None
    )

def sanitize(value: str) -> str:
    return (value or "").strip()

def validate(value: str) -> Optional[str]:
    return value if value and value.isalnum() else None
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Shared source
   - Prompt and test walls appear (top center)
   - "Same specification" label
   - Arrows pointing down to both paths

2. **Frame 90-180 (3-6s):** Grounding indicators
   - Left: "Grounding: OOP Codebase" appears
   - Right: "Grounding: Functional Codebase" appears
   - Green highlighting

3. **Frame 180-300 (6-10s):** Code generation
   - Left: OOP code flows in (classes, methods)
   - Right: Functional code flows in (pipe, pure functions)
   - Both animated with green tint

4. **Frame 300-420 (10-14s):** Comparison
   - Highlight key differences
   - Class structure vs function composition
   - Both structured differently

5. **Frame 420-540 (14-18s):** Both pass
   - Left: Green checkmark
   - Right: Green checkmark
   - "Same behavior, different style"

6. **Frame 540-600 (18-20s):** Hold on insight
   - Both valid implementations
   - Grounding determines HOW

### Visual Design: Split Comparison

```
             ┌──────────────────────────────┐
             │  Same Prompt + Same Tests    │
             │  ┌────────┐    █ █ █ █      │
             │  │ PROMPT │    (walls)       │
             │  └────────┘                  │
             └──────────────────────────────┘
                    ╱               ╲
                   ╱                 ╲
                  ▼                   ▼
    ┌────────────────────┐  ┌────────────────────┐
    │ Grounding:         │  │ Grounding:         │
    │ OOP Codebase       │  │ Functional Codebase│
    ├────────────────────┤  ├────────────────────┤
    │ class UserParser:  │  │ def parse_user_id: │
    │   def __init__():  │  │   return pipe(     │
    │     ...            │  │     input_str,     │
    │   def parse():     │  │     sanitize,      │
    │     ...            │  │     validate,      │
    │   def _sanitize(): │  │     ...            │
    │     ...            │  │   )                │
    └────────────────────┘  └────────────────────┘
           ✓                        ✓
      All tests pass          All tests pass

    ═══════════════════════════════════════════
    │ Same behavior. Different style.         │
    │ Grounding determines HOW.               │
    ═══════════════════════════════════════════
```

### Code Structure (Remotion)

```typescript
const GroundingComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Shared source visibility
  const sourceOpacity = interpolate(
    frame,
    [0, 60],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Grounding labels
  const groundingOpacity = interpolate(
    frame,
    [90, 140],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Code appearances
  const oopCodeOpacity = interpolate(
    frame,
    [180, 240],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const functionalCodeOpacity = interpolate(
    frame,
    [200, 260],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Checkmarks
  const checkmarkOpacity = interpolate(
    frame,
    [420, 460],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Insight text
  const insightOpacity = interpolate(
    frame,
    [540, 580],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Shared source at top */}
      <SharedSource opacity={sourceOpacity} />

      {/* Diverging arrows */}
      <DivergingArrows opacity={sourceOpacity} />

      {/* Left: OOP path */}
      <div style={{
        position: 'absolute',
        left: 60,
        top: 280,
      }}>
        <GroundingLabel
          text="Grounding: OOP Codebase"
          opacity={groundingOpacity}
        />
        <CodeBlock
          code={oopCode}
          opacity={oopCodeOpacity}
          style="oop"
        />
        <Checkmark opacity={checkmarkOpacity} />
      </div>

      {/* Right: Functional path */}
      <div style={{
        position: 'absolute',
        right: 60,
        top: 280,
      }}>
        <GroundingLabel
          text="Grounding: Functional Codebase"
          opacity={groundingOpacity}
        />
        <CodeBlock
          code={functionalCode}
          opacity={functionalCodeOpacity}
          style="functional"
        />
        <Checkmark opacity={checkmarkOpacity} />
      </div>

      {/* Insight */}
      <InsightText
        lines={[
          "Same behavior. Different style.",
          "Grounding determines HOW."
        ]}
        opacity={insightOpacity}
      />
    </AbsoluteFill>
  );
};
```

### Shared Source Component

```typescript
const SharedSource: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <div style={{
      position: 'absolute',
      top: 40,
      left: '50%',
      transform: 'translateX(-50%)',
      opacity,
      display: 'flex',
      flexDirection: 'column',
      alignItems: 'center',
    }}>
      <div style={{
        fontSize: 16,
        color: '#888',
        marginBottom: 16,
      }}>
        Same Prompt + Same Tests
      </div>
      <div style={{ display: 'flex', gap: 30 }}>
        {/* Prompt mini */}
        <div style={{
          padding: '8px 16px',
          background: 'rgba(74, 144, 217, 0.2)',
          border: '1px solid #4A90D9',
          borderRadius: 6,
          fontSize: 12,
          color: '#4A90D9',
        }}>
          PROMPT
        </div>
        {/* Test walls mini */}
        <div style={{
          padding: '8px 16px',
          background: 'rgba(217, 148, 74, 0.2)',
          border: '1px solid #D9944A',
          borderRadius: 6,
          fontSize: 12,
          color: '#D9944A',
        }}>
          TESTS ████
        </div>
      </div>
    </div>
  );
};
```

### Easing

- Source fade: `easeOutCubic`
- Code flow: `easeOutCubic`
- Checkmark: `easeOutBack`
- Insight: `easeOutCubic`

## Narration Sync

> "Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system."

The two different styles appear during this narration, showing how grounding produces different implementations from the same specification.

## Audio Notes

- Soft "split" sound as paths diverge
- Code appearance sounds
- Two checkmark sounds (same tone)
- Contemplative tone for insight

## Visual Style Notes

- Both paths are equally valid
- Green connects to grounding theme
- Key differences highlighted
- Same checkmarks = same behavior
- Style is a choice, not right/wrong

## Transition

Continues into Section 3.16 showing success flowing to the grounding database.
