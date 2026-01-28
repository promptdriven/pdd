# Section 2.9: Plastic Part Dissolves and Regenerates

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 6:55 - 7:05

## Visual Description

Focus on the right side (mold/manufacturing). A plastic part dissolves into particles - then instantly regenerates, identical. The visual proof that outputs are disposable when you have the specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Focus on single part and mold
- Dark background (#1a1a2e)

### Visual Elements

1. **The Plastic Part**
   - Simple geometric shape (same as previous sections)
   - Color: Amber (#D9944A)
   - Positioned center-right of frame

2. **The Mold (Background)**
   - Visible but slightly faded
   - Still glowing with value aura
   - The source of all parts

3. **Dissolution Effect**
   - Part breaks into particles
   - Particles scatter/fade
   - Quick, satisfying dissolution

4. **Regeneration Effect**
   - New particles coalesce
   - Form identical part
   - "Pop" into existence

### Animation Sequence

1. **Frame 0-30 (0-1s):** Part visible, mold glowing in background
   - Setup the scene
   - Part is clearly "just output"

2. **Frame 30-90 (1-3s):** Dissolution begins
   - Part starts breaking apart
   - Particles scatter outward
   - Color fades as it dissolves

3. **Frame 90-120 (3-4s):** Fully dissolved
   - Part is gone
   - Only particles/dust remain
   - Beat of absence

4. **Frame 120-180 (4-6s):** Regeneration begins
   - New particles flow from mold direction
   - Coalesce at original position
   - Color returns

5. **Frame 180-240 (6-8s):** Part fully reformed
   - Identical to before
   - Satisfying "snap" into place
   - Slight glow/pulse on completion

6. **Frame 240-300 (8-10s):** Hold
   - Part exists again
   - Mold continues glowing
   - Message clear: infinitely reproducible

### Particle System Specifications

**Dissolution:**
- Particle count: 200-500
- Direction: Outward, slightly random
- Speed: Fast initial burst, then drift
- Size: Small (2-5px)
- Color: Amber → Gray → Fade
- Easing: `easeOutQuad`

**Regeneration:**
- Particle count: Same 200-500
- Direction: Inward from edges/mold
- Speed: Accelerating toward center
- Size: Small → Original
- Color: Gray → Amber
- Easing: `easeInCubic`

### Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Background mold with aura */}
  <MoldBackground glowing={true} opacity={0.6} />

  {/* Part lifecycle */}
  <Sequence from={0} durationInFrames={90}>
    <PlasticPart state="solid" />
  </Sequence>

  <Sequence from={30} durationInFrames={90}>
    <DissolutionEffect
      particleCount={300}
      duration={60}
    />
  </Sequence>

  <Sequence from={120} durationInFrames={60}>
    <RegenerationEffect
      particleCount={300}
      sourceDirection="mold"
      duration={60}
    />
  </Sequence>

  <Sequence from={180}>
    <PlasticPart state="solid" showCompletionGlow={true} />
  </Sequence>
</Sequence>
```

### Particle Effect Implementation

```typescript
const ParticleSystem = ({
  count,
  mode, // 'dissolve' | 'regenerate'
  progress // 0-1
}) => {
  const particles = useMemo(() =>
    Array.from({ length: count }, (_, i) => ({
      id: i,
      angle: (i / count) * Math.PI * 2 + Math.random() * 0.5,
      distance: Math.random() * 100 + 50,
      delay: Math.random() * 0.3
    })), [count]);

  return particles.map(p => {
    const particleProgress = Math.max(0, Math.min(1,
      (progress - p.delay) / (1 - p.delay)
    ));

    const distance = mode === 'dissolve'
      ? particleProgress * p.distance
      : (1 - particleProgress) * p.distance;

    return (
      <Particle
        key={p.id}
        x={Math.cos(p.angle) * distance}
        y={Math.sin(p.angle) * distance}
        opacity={mode === 'dissolve' ? 1 - particleProgress : particleProgress}
      />
    );
  });
};
```

## Narration Sync

> "The plastic part? Disposable. Regenerate it at will."

## Audio Notes

- Dissolution: Soft "whoosh" or scatter sound
- Beat of silence when part is gone
- Regeneration: Reverse sound or "crystallize" effect
- Completion: Subtle "click" or "snap"

## Visual Style Notes

- Should feel almost magical but grounded
- The dissolution is not violent or sad
- The regeneration is effortless
- Key message: this is EASY when you have the mold

## Transition

Morphs into Section 2.10 where the mold becomes a PROMPT document and the plastic becomes code.
