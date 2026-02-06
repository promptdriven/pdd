# Section 2.3: Parts Eject (Counter Animation)

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 7:10 - 7:37

## Visual Description

The mold opens and identical parts eject, one after another. A counter shows the exponential scale: 1... 10... 100... 10,000... The key message: make the mold once, produce unlimited identical parts.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark industrial (#1a1a2e) or continue from video with overlay

### Visual Elements

1. **Mold Animation (Stylized)**
   - Cross-section view of mold
   - Two halves separate
   - Part ejects from center
   - Mold closes, cycle repeats

2. **Part Visualization**
   - Simple geometric shape (could be abstract "widget")
   - Color: Cooled amber (#D9944A)
   - Drops/slides into collection area
   - Parts accumulate or flow off-screen

3. **Counter Display**
   - Position: Bottom-right or top-right
   - Large numerals, monospace font
   - Counts: 1 → 10 → 100 → 1,000 → 10,000
   - Accelerating animation (logarithmic feel)

4. **Cycle Speed**
   - Starts slow (1 part every 2 seconds)
   - Accelerates (parts blur together)
   - Suggests infinite reproducibility

### Animation Sequence

1. **Frame 0-60 (0-2s):** First part ejects
   - Mold opens slowly
   - Part visible, ejects
   - Counter: 1

2. **Frame 60-120 (2-4s):** Parts 2-10
   - Cycle speeds up
   - Counter increments
   - Parts begin accumulating

3. **Frame 120-240 (4-8s):** Parts 10-100
   - Rapid cycling
   - Parts become stream
   - Counter accelerates

4. **Frame 240-420 (8-14s):** Parts 100-10,000
   - Very fast, almost blur
   - Counter spins
   - Overwhelming quantity

5. **Frame 420-600 (14-20s):** Hold on scale
   - Counter settles at 10,000+
   - Parts continue flowing
   - Emphasis: unlimited production

### Counter Styling

```css
.part-counter {
  font-family: 'JetBrains Mono', monospace;
  font-size: 72px;
  color: #FFFFFF;
  text-shadow: 0 0 20px rgba(74, 144, 217, 0.5);
}

.counter-label {
  font-size: 18px;
  color: #888;
  text-transform: uppercase;
  letter-spacing: 2px;
}
```

### Easing

- Mold open/close: `easeInOutQuad`
- Part eject: `easeOutCubic`
- Counter increment: Custom acceleration curve (slow → fast)

## Narration Sync

> "Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Mold animation */}
  <MoldCycleAnimation
    cycleSpeed={frame => Math.max(10, 60 - frame / 10)}
    partColor="#D9944A"
  />

  {/* Parts accumulation */}
  <PartsAccumulator
    spawnRate={frame => Math.min(10, 1 + frame / 60)}
  />

  {/* Counter */}
  <PartCounter
    values={[1, 10, 100, 1000, 10000]}
    timings={[60, 120, 240, 420, 540]}
    format="comma-separated"
  />

  {/* Label */}
  <CounterLabel text="PARTS PRODUCED" />
</Sequence>
```

## Visual Style Notes

- The mold should be stylized/abstract, not photorealistic
- Parts can be simple shapes (cubes, cylinders, or abstract "widgets")
- The counter is the star - make numbers prominent
- 3Blue1Brown aesthetic: clean, mathematical, satisfying

## Part Shape Options

1. **Abstract Widget:** Simple geometric shape unique to this video
2. **Recognizable Object:** Bottle cap, container lid, simple tool
3. **The Sock:** Callback to Part 1 - plastic sock-shaped parts

## Transition

Cut to defect discovery (Section 2.4).
