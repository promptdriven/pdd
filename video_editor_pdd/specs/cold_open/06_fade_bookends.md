[Remotion] Fade-In / Fade-Out Bookends

# Section 0.6: Fade Bookends — Black In/Out

**Tool:** Remotion
**Duration:** ~1s in + ~1s out
**Timestamp:** 0:00 - 0:01 (in), 0:14.68 - 0:15.68 (out)

## Visual Description
The cold open begins with a fade-in from solid black and ends with a fade-out to solid black. These bookend transitions frame the section as a self-contained cinematic opening. The fade-in reveals the Veo desk footage gradually, giving the narration a moment to settle before the visuals fully arrive. The fade-out creates a definitive end-beat before the next section begins.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Overlay: solid black (#000000) layer on top of all other layers
- Z-index: topmost (above Veo, above title card, above subtitles)

### Chart/Visual Elements
- Black overlay: full-screen solid fill (#000000)
- No graphic elements — purely an opacity animation on a black rectangle

### Animation Sequence

#### Fade-In (opening)
1. **Frame 0 (0.0s):** Black overlay at 100% opacity — screen is fully black
2. **Frame 10 (0.33s):** 67% opacity — Veo footage begins to show through
3. **Frame 20 (0.67s):** 33% opacity — mostly visible
4. **Frame 30 (1.0s):** 0% opacity — black overlay fully transparent, removed from render

#### Fade-Out (closing)
1. **Frame 440 (14.67s):** Black overlay at 0% opacity — re-enters render tree
2. **Frame 450 (15.0s):** 33% opacity — footage begins to darken
3. **Frame 460 (15.33s):** 67% opacity — mostly black
4. **Frame 470 (15.67s):** 100% opacity — screen is fully black

### Typography
- None

### Easing
- Fade-in: `easeOutQuad` (fast reveal, gentle settle)
- Fade-out: `easeInQuad` (gentle start, firm close)

## Narration Sync
> Fade-in: "If you use Cursor..."
> Fade-out: "...still patching?"

The fade-in overlaps the first word of narration. The fade-out begins just as "patching?" trails off, reinforcing the question's weight with darkness.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={470}>
  {/* All other layers rendered below */}
  <AbsoluteFill style={{ zIndex: 100 }}>
    {/* Fade-in from black */}
    {frame < 30 && (
      <div
        style={{
          backgroundColor: '#000000',
          opacity: interpolate(frame, [0, 30], [1, 0], { easing: Easing.out(Easing.quad) }),
          width: '100%',
          height: '100%',
        }}
      />
    )}
    {/* Fade-out to black */}
    {frame > 440 && (
      <div
        style={{
          backgroundColor: '#000000',
          opacity: interpolate(frame, [440, 470], [0, 1], { easing: Easing.in(Easing.quad) }),
          width: '100%',
          height: '100%',
        }}
      />
    )}
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "fade_in": {
    "start_frame": 0,
    "end_frame": 30,
    "duration_seconds": 1.0,
    "easing": "easeOutQuad"
  },
  "fade_out": {
    "start_frame": 440,
    "end_frame": 470,
    "duration_seconds": 1.0,
    "easing": "easeInQuad"
  },
  "color": "#000000",
  "z_index": "topmost"
}
```

---
