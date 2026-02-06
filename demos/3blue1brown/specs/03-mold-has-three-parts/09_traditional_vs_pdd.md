# Section 3.9: Traditional vs PDD

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 12:55 - 13:10

## Visual Description

Split screen comparison. LEFT: Traditional development - bug found → patch code → similar bug elsewhere → patch again → different bug → patch again (cycle). RIGHT: PDD - bug found → add test (`pdd bug`) → regenerate (`pdd fix`) → bug impossible forever.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Vertical split at center

### Animation Elements

1. **Left Side: Traditional**
   - Title: "Traditional"
   - Cycling animation of patch-find-patch
   - Code blocks with band-aids/patches
   - Red indicators for recurring bugs
   - Endless loop feeling

2. **Right Side: PDD**
   - Title: "PDD"
   - Linear progression: bug → test → regenerate → done
   - Mold wall materializing
   - Green checkmark at end
   - Terminal: `pdd bug` → `pdd fix` → ✓

3. **Center Divider**
   - Clean vertical line
   - Subtle gradient

### Animation Sequence - Left (Traditional)

1. **Frame 0-60 (0-2s):** Bug found
   - Code block appears
   - Red highlight on bug
   - "BUG" label

2. **Frame 60-120 (2-4s):** Patch applied
   - Band-aid/patch visual covers bug
   - "Fixed?" appears

3. **Frame 120-180 (4-6s):** Similar bug elsewhere
   - Another code block appears
   - Same type of bug highlighted
   - "BUG" label (same issue)

4. **Frame 180-240 (6-8s):** Patch again
   - Another patch applied
   - Cycle continues

5. **Frame 240-450 (8-15s):** Loop indicator
   - Arrow showing cycle
   - "Repeat..." label
   - Patches accumulating

### Animation Sequence - Right (PDD)

1. **Frame 0-60 (0-2s):** Bug found
   - Code block appears
   - Red highlight on bug
   - "BUG" label

2. **Frame 60-150 (2-5s):** Add test
   - Terminal: `pdd bug user_parser`
   - Wall materializes
   - Click sound

3. **Frame 150-270 (5-9s):** Regenerate
   - Terminal: `pdd fix user_parser`
   - Code dissolves and regenerates
   - New code conforms to wall

4. **Frame 270-450 (9-15s):** Done forever
   - Green checkmark
   - "Bug impossible forever"
   - Wall glows permanently
   - No more cycle

### Visual Design: Split Screen

```
┌────────────────────────┬────────────────────────┐
│      TRADITIONAL       │          PDD           │
├────────────────────────┼────────────────────────┤
│                        │                        │
│   ┌────┐  BUG         │   ┌────┐  BUG         │
│   │████│───►          │   │████│───►          │
│   └────┘               │   └────┘               │
│      │                 │      │                 │
│      ▼                 │      ▼                 │
│   ┌────┐  patch       │   █ ← wall             │
│   │🩹  │               │   │                    │
│   └────┘               │   │ pdd bug           │
│      │                 │      │                 │
│      ▼                 │      ▼                 │
│   ┌────┐  BUG again!  │   ┌────┐  regenerate  │
│   │████│               │   │▓▓▓▓│               │
│   └────┘               │   └────┘               │
│      │                 │      │                 │
│      ▼                 │      ▼                 │
│     ...                │     ✓ Done forever    │
│   (cycle)              │                        │
│                        │                        │
└────────────────────────┴────────────────────────┘
```

### Code Structure (Remotion)

```typescript
const TraditionalVsPdd: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Left side: Traditional */}
      <div style={{
        position: 'absolute',
        left: 0,
        width: '50%',
        height: '100%',
        borderRight: '2px solid #333',
      }}>
        <SectionTitle text="Traditional" />
        <TraditionalFlow frame={frame} />
      </div>

      {/* Right side: PDD */}
      <div style={{
        position: 'absolute',
        right: 0,
        width: '50%',
        height: '100%',
      }}>
        <SectionTitle text="PDD" />
        <PddFlow frame={frame} />
      </div>
    </AbsoluteFill>
  );
};
```

### Traditional Flow Component

```typescript
const TraditionalFlow: React.FC<{ frame: number }> = ({ frame }) => {
  const cyclePosition = frame % 180; // Looping cycle

  return (
    <div style={{ padding: 40 }}>
      {/* Bug 1 */}
      <FlowStep
        icon="bug"
        label="Bug found"
        active={cyclePosition < 60}
      />
      <Arrow />
      {/* Patch 1 */}
      <FlowStep
        icon="bandaid"
        label="Patch code"
        active={cyclePosition >= 60 && cyclePosition < 90}
      />
      <Arrow />
      {/* Bug 2 */}
      <FlowStep
        icon="bug"
        label="Similar bug elsewhere"
        active={cyclePosition >= 90 && cyclePosition < 120}
        color="#D94A4A"
      />
      <Arrow />
      {/* Patch 2 */}
      <FlowStep
        icon="bandaid"
        label="Patch again..."
        active={cyclePosition >= 120}
      />
      {/* Loop arrow */}
      <LoopArrow opacity={frame > 240 ? 1 : 0} />
    </div>
  );
};
```

### PDD Flow Component

```typescript
const PddFlow: React.FC<{ frame: number }> = ({ frame }) => {
  return (
    <div style={{ padding: 40 }}>
      {/* Bug found */}
      <FlowStep
        icon="bug"
        label="Bug found"
        active={frame < 60}
      />
      <Arrow />
      {/* Add test */}
      <FlowStep
        icon="wall"
        label="Add test (pdd bug)"
        active={frame >= 60 && frame < 150}
        terminal="$ pdd bug user_parser"
      />
      <Arrow />
      {/* Regenerate */}
      <FlowStep
        icon="regenerate"
        label="Regenerate (pdd fix)"
        active={frame >= 150 && frame < 270}
        terminal="$ pdd fix user_parser"
      />
      <Arrow />
      {/* Done forever */}
      <FlowStep
        icon="checkmark"
        label="Bug impossible forever"
        active={frame >= 270}
        color="#5AAA6E"
        final={true}
      />
    </div>
  );
};
```

### Easing

- Step transitions: `easeOutCubic`
- Arrow draws: `easeOutQuad`
- Loop arrow: `easeInOutSine` (pulsing)
- Checkmark: `easeOutBack`

## Narration Sync

> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

The left side shows the cycle during "traditional development", the right side completes during "everywhere, forever".

## Audio Notes

- Left side: Repetitive, slightly discordant sounds
- Right side: Progressive, resolving tones
- Final checkmark: Satisfying completion sound
- Contrast between endless and final

## Visual Style Notes

- Left side should feel frustrating, cyclical
- Right side should feel decisive, final
- The contrast is stark and intentional
- Terminal commands are subtle but visible
- This is the key comparison that sells PDD

## Transition

Hard cut to Section 3.10 introducing Prompt Capital with the injection nozzle highlighting.
