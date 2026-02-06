# Section 3.12: Prompt Variations

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 13:40 - 14:00

## Visual Description

The same prompt generates code twice. The code is slightly different each time—different variable names, slightly different structure—but both versions pass all tests. Terminal: `pdd generate user_parser.prompt` runs twice, different outputs, both valid. This shows that implementation can vary while behavior is fixed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Split view showing two generations

### Animation Elements

1. **Single Prompt Source**
   - Same `user_parser.prompt` document
   - Blue glow, center-top position
   - Arrows pointing to both outputs

2. **Two Code Outputs**
   - Side by side
   - Visibly different implementations
   - Both syntactically valid
   - Different variable names, structure

3. **Test Verification**
   - Both outputs show green checkmarks
   - "All tests pass" for both
   - Same constraints, different implementations

4. **Terminal Overlay**
   - Shows `pdd generate user_parser.prompt` twice
   - Different generation timestamps/seeds
   - Both succeed

### Code Variants

**Version A:**
```python
def parse_user_id(input_str):
    if not input_str or not input_str.strip():
        return None
    cleaned = input_str.strip()
    if not cleaned.isalnum():
        return None
    return cleaned
```

**Version B:**
```python
def parse_user_id(raw_input):
    sanitized = (raw_input or "").strip()
    if len(sanitized) == 0:
        return None
    return sanitized if sanitized.isalnum() else None
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Prompt shown
   - `user_parser.prompt` in center-top
   - "Same prompt" label
   - Arrows indicate it will go two places

2. **Frame 90-180 (3-6s):** First generation
   - Left side: Terminal runs `pdd generate`
   - Code appears (Version A)
   - Tests run → checkmark

3. **Frame 180-270 (6-9s):** Second generation
   - Right side: Terminal runs `pdd generate`
   - Code appears (Version B)
   - Tests run → checkmark
   - Visibly different from Version A

4. **Frame 270-360 (9-12s):** Comparison highlight
   - Differences highlighted
   - `input_str` vs `raw_input`
   - Different structure
   - Both valid

5. **Frame 360-450 (12-15s):** Key insight
   - "Code varies. Behavior fixed."
   - Both have same green checkmarks
   - Hold on this insight

### Visual Design: Variation Comparison

```
                 ┌─────────────────────┐
                 │  user_parser.prompt │
                 │  (SAME PROMPT)      │
                 └──────────┬──────────┘
                      ╱           ╲
                     ╱             ╲
                    ▼               ▼
        ┌──────────────────┐  ┌──────────────────┐
        │   Generation A   │  │   Generation B   │
        ├──────────────────┤  ├──────────────────┤
        │ def parse_user_  │  │ def parse_user_  │
        │   id(input_str): │  │   id(raw_input): │
        │   if not input_  │  │   sanitized =    │
        │     str or...    │  │     (raw_input   │
        │   cleaned =      │  │       or "")...  │
        │     input_str... │  │   if len(sanit...|
        └──────────────────┘  └──────────────────┘
               ✓                     ✓
         All tests pass        All tests pass

        ═══════════════════════════════════════
        │ Code varies. Behavior is fixed.     │
        ═══════════════════════════════════════
```

### Code Structure (Remotion)

```typescript
const PromptVariations: React.FC = () => {
  const frame = useCurrentFrame();

  // Prompt visibility
  const promptOpacity = interpolate(
    frame,
    [0, 60],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Version A appearance
  const versionAOpacity = interpolate(
    frame,
    [90, 150],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Version B appearance
  const versionBOpacity = interpolate(
    frame,
    [180, 240],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Insight text
  const insightOpacity = interpolate(
    frame,
    [360, 400],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Prompt source */}
      <PromptDocument
        filename="user_parser.prompt"
        opacity={promptOpacity}
        position={{ x: 960, y: 80 }}
        label="Same Prompt"
      />

      {/* Diverging arrows */}
      <DivergingArrows opacity={promptOpacity} />

      {/* Version A (left) */}
      <CodeGeneration
        version="A"
        code={versionACode}
        opacity={versionAOpacity}
        position="left"
        showCheckmark={frame > 170}
      />

      {/* Version B (right) */}
      <CodeGeneration
        version="B"
        code={versionBCode}
        opacity={versionBOpacity}
        position="right"
        showCheckmark={frame > 260}
      />

      {/* Difference highlights */}
      {frame > 270 && (
        <DifferenceHighlights
          opacity={interpolate(frame, [270, 300], [0, 1])}
        />
      )}

      {/* Key insight */}
      <InsightText
        text="Code varies. Behavior is fixed."
        opacity={insightOpacity}
      />

      {/* Terminal showing both generations */}
      <TerminalOverlay
        lines={[
          frame > 90 ? "$ pdd generate user_parser.prompt" : "",
          frame > 150 ? "Generated: parser_v1.py ✓" : "",
          frame > 180 ? "$ pdd generate user_parser.prompt" : "",
          frame > 240 ? "Generated: parser_v2.py ✓" : "",
        ]}
      />
    </AbsoluteFill>
  );
};
```

### Difference Highlights

```typescript
const DifferenceHighlights: React.FC<{ opacity: number }> = ({ opacity }) => {
  const highlights = [
    { side: 'left', line: 1, text: 'input_str' },
    { side: 'right', line: 1, text: 'raw_input' },
    { side: 'left', line: 3, text: 'cleaned' },
    { side: 'right', line: 2, text: 'sanitized' },
  ];

  return (
    <g opacity={opacity}>
      {highlights.map((h, i) => (
        <HighlightBox
          key={i}
          side={h.side}
          line={h.line}
          color="#FFAA55" // Amber highlight
        />
      ))}
    </g>
  );
};
```

### Easing

- Prompt fade: `easeOutCubic`
- Arrow draw: `easeOutQuad`
- Code appearance: `easeOutCubic`
- Highlight pulse: `easeInOutSine`
- Insight text: `easeOutCubic`

## Narration Sync

> "And here's something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."

Both versions appear during "implementation can vary". The checkmarks appear during "behavior" and "contract is fixed".

## Audio Notes

- Two distinct "generation" sounds
- Both followed by success tones
- Subtle highlight sound for differences
- Contemplative tone for the insight

## Visual Style Notes

- Same prompt → visibly different code
- But same outcome (tests pass)
- Highlights show differences clearly
- Insight is the takeaway message
- This demonstrates prompt flexibility

## Transition

Continues into Section 3.13 showing how a small prompt governs a large file.
