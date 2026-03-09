[split:]

# Section 2.12: Split Screen — Ocean & Forest Reprise

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:33 - 0:36

## Visual Description
The ocean/forest split screen returns with a different visual treatment. This time, the divider sweeps horizontally from left to right like a wipe transition, revealing the forest clip replacing the ocean clip. The wipe pauses at center for a beat, showing the split, then continues rightward. This creates a more dynamic version of the earlier static split.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Black (#000000)

### Chart/Visual Elements
- Base layer: Ocean wave sunset clip, full-frame 1920x1080
- Reveal layer: Forest canopy aerial clip, full-frame 1920x1080, clipped by wipe position
- Wipe edge: Vertical gradient band, 8px wide, white (#FFFFFF) to transparent, at the clip boundary
- Wipe glow: 40px soft amber glow (#F59E0B at 15% opacity) trailing the wipe edge
- Bottom bar: Thin progress indicator, 4px, at Y=1076, fills left-to-right tracking wipe position
  - Color: gradient #F59E0B to #34D399

### Animation Sequence
1. **Frame 0-30 (0-1s):** Wipe edge moves from X=0 to X=960 (center). Forest clip is progressively revealed from left.
2. **Frame 30-60 (1-2s):** Wipe holds at X=960 — split screen visible for 1 second. Both clips play side by side.
3. **Frame 60-85 (2-2.83s):** Wipe continues from X=960 to X=1920, fully revealing forest clip.
4. **Frame 85-90 (2.83-3s):** Hold on full forest frame. Wipe glow fades out.

### Typography
- None — pure visual transition

### Easing
- Wipe movement (0-30): `easeOutQuad`
- Wipe hold (30-60): static
- Wipe movement (60-85): `easeInQuad`
- Bottom bar: matches wipe position

## Narration Sync
> (No narration — visual transition beat)

## Code Structure (Remotion)
```typescript
<Sequence from={990} durationInFrames={90}>
  <WipeTransition
    fromSrc={staticFile("veo/ocean_wave_sunset.mp4")}
    toSrc={staticFile("veo/forest_canopy_aerial.mp4")}
    pauseAtCenter={true}
    pauseDuration={30}
    wipeGlowColor="#F59E0B"
  />
  <ProgressBar
    y={1076}
    height={4}
    gradientStart="#F59E0B"
    gradientEnd="#34D399"
  />
</Sequence>
```

## Data Points
```json
{
  "fromClip": "veo/ocean_wave_sunset.mp4",
  "toClip": "veo/forest_canopy_aerial.mp4",
  "wipeGlowColor": "#F59E0B",
  "pauseAtCenter": true,
  "pauseFrames": 30
}
```

---
