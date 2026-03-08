[Remotion] Crossfade Transition — Shot 1 to Shot 2

# Section 0.5: Crossfade Transition

**Tool:** Remotion
**Duration:** ~0.67s (20 frames)
**Timestamp:** 0:08 - 0:08.67

## Visual Description
A smooth crossfade dissolve between the wide desk shot (cold_open_veo_01) and the close-up glasses shot (cold_open_veo_02). The transition is deliberately unhurried — the wide shot's opacity decreases while the close-up simultaneously increases, creating a brief double-exposure moment where both shots blend. This organic transition mirrors the narration shifting from anecdote to thesis.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: composed from two Veo layers
- No additional graphic elements

### Chart/Visual Elements
- Layer A (outgoing): `veo/cold_open_veo_01.mp4` — developer desk wide shot
- Layer B (incoming): `veo/cold_open_veo_02.mp4` — developer close-up
- Blend mode: normal (opacity crossfade)
- No additional wipes, pushes, or graphic transitions

### Animation Sequence
1. **Frame 240 (8.0s):** Layer A at 100% opacity, Layer B at 0% opacity
2. **Frame 245 (8.17s):** Layer A at 75%, Layer B at 25% — double exposure begins
3. **Frame 250 (8.33s):** Layer A at 50%, Layer B at 50% — peak blend
4. **Frame 255 (8.50s):** Layer A at 25%, Layer B at 75%
5. **Frame 260 (8.67s):** Layer A at 0%, Layer B at 100% — transition complete

### Typography
- None — subtitle track continues independently (03_subtitle_track.md)

### Easing
- Layer A opacity out: `easeInOutCubic`
- Layer B opacity in: `easeInOutCubic`

## Narration Sync
> "...she stopped darning. Code just got that cheap."

The crossfade occurs during the pause between "she stopped darning" and "Code just got that cheap" — the silence gap (0.3s) plus the start of the new sentence.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={470}>
  {/* Outgoing shot */}
  <Sequence from={0} durationInFrames={260}>
    <Video
      src={staticFile('veo/cold_open_veo_01.mp4')}
      style={{
        opacity: interpolate(frame, [240, 260], [1, 0], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }),
      }}
    />
  </Sequence>
  {/* Incoming shot */}
  <Sequence from={240} durationInFrames={230}>
    <Video
      src={staticFile('veo/cold_open_veo_02.mp4')}
      style={{
        opacity: interpolate(frame, [240, 260], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }),
      }}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "transition_type": "crossfade",
  "start_frame": 240,
  "end_frame": 260,
  "duration_frames": 20,
  "duration_seconds": 0.67,
  "easing": "easeInOutCubic",
  "layer_a": "veo/cold_open_veo_01.mp4",
  "layer_b": "veo/cold_open_veo_02.mp4"
}
```

---
