# Section 2.8: Value Aura Effect

**Tool:** Remotion (overlay on Veo footage or fully animated)
**Duration:** ~15 seconds
**Timestamp:** 8:43 - 9:03

## Visual Description

On the split screen, a glowing aura effect reveals where value truly lives. LEFT: The aura surrounds the wooden chair - the object itself. RIGHT: The aura surrounds the MOLD, not the plastic part. Value has migrated from output to specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Overlay on split screen from Section 2.7
- Or transition to stylized version

### Aura Effect

**Aura Characteristics:**
- Soft, glowing outline
- Pulsing subtly (breathing effect)
- Color: White/gold gradient
- Feathered edges (not sharp)
- Semi-transparent (30-50% opacity)

**Left Side Aura:**
- Surrounds the wooden chair/object
- Envelops the craftsman's work
- Message: "Value is HERE, in what I made"

**Right Side Aura:**
- Surrounds the MOLD (not the plastic parts)
- Parts that eject are notably NOT glowing
- Message: "Value is HERE, in the specification"

### Animation Sequence

1. **Frame 0-90 (0-3s):** Split screen holds from previous section
   - Subtle preparation for effect

2. **Frame 90-180 (3-6s):** Left aura appears
   - Fades in around the wooden chair
   - Grows and pulses
   - Clear emphasis: the OBJECT glows

3. **Frame 180-270 (6-9s):** Right aura appears
   - Fades in around the MOLD
   - Plastic parts remain un-glowing
   - Clear emphasis: the MOLD glows, outputs don't

4. **Frame 270-360 (9-12s):** Both auras visible
   - Side-by-side comparison
   - Pulsing in sync
   - The contrast is clear

5. **Frame 360-450 (12-15s):** Hold and emphasize
   - Labels appear (optional):
     - LEFT: "Value in Object"
     - RIGHT: "Value in Specification"

### Aura Technical Implementation

```typescript
// Aura component
const ValueAura = ({
  maskPath,
  color = "#FFD700",
  pulseSpeed = 60
}) => {
  const frame = useCurrentFrame();
  const pulse = 1 + 0.05 * Math.sin(frame / pulseSpeed * Math.PI * 2);

  return (
    <div style={{
      filter: `blur(20px)`,
      opacity: 0.4,
      transform: `scale(${pulse})`,
      background: `radial-gradient(ellipse, ${color}, transparent)`
    }}>
      <svg>
        <path d={maskPath} fill="white" />
      </svg>
    </div>
  );
};
```

### Color Specifications

- Aura base: White (#FFFFFF)
- Aura gradient: White → Gold (#FFD700) → Transparent
- Pulse range: 95% to 105% scale
- Blur radius: 15-25px

### Label Styling (Optional)

```css
.value-label {
  font-family: sans-serif;
  font-size: 24px;
  color: #FFFFFF;
  text-shadow: 0 2px 10px rgba(0, 0, 0, 0.5);
  text-transform: uppercase;
  letter-spacing: 3px;
}
```

## Narration Sync

> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."
>
> "In molding, value lives in the specification—the mold. The plastic part? Disposable. Regenerate it at will."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Split screen base (video or animated) */}
  <SplitScreenBase left={craftsmanScene} right={moldScene} />

  {/* Left aura */}
  <Sequence from={90}>
    <ValueAura
      side="left"
      target="chair"
      fadeInDuration={90}
    />
  </Sequence>

  {/* Right aura */}
  <Sequence from={180}>
    <ValueAura
      side="right"
      target="mold"
      fadeInDuration={90}
    />
  </Sequence>

  {/* Labels */}
  <Sequence from={360}>
    <SplitLabel
      left="Value in Object"
      right="Value in Specification"
    />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- The aura should feel almost sacred/precious
- Not cheesy or over-the-top
- Subtle enough to be elegant
- Clear enough to communicate the point
- 3Blue1Brown aesthetic: mathematical beauty

## Key Visual Contrast

| Left (Craft) | Right (Mold) |
|--------------|--------------|
| Chair glows | Mold glows |
| Craftsman's work is precious | Parts are disposable |
| Lose the chair = lose everything | Lose a part = regenerate |

## Transition

Right side continues into Section 2.9 (plastic part dissolves and regenerates).
