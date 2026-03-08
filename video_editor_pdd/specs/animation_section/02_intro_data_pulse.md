[Remotion]

# Section 1.2: Intro Data Pulse

**Tool:** Remotion
**Duration:** ~2.5s (75 frames)
**Timestamp:** 0:01 - 0:03

## Visual Description
A pulsing concentric ring visualization radiates outward from the center of the screen, representing data flowing through the integration test pipeline. Three rings expand sequentially with staggered timing, each ring glowing in a different shade of blue/cyan. A central dot pulses with a heartbeat rhythm. Small data labels ("Section 1", "Remotion", "30fps") orbit around the outer ring.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (slate-950)
- No grid lines

### Chart/Visual Elements
- **Central dot:** 12px diameter, #60A5FA, pulsing between 8-16px with glow
- **Ring 1 (inner):** 120px radius, 2px stroke, #3B82F6 (blue-500), 80% opacity
- **Ring 2 (middle):** 240px radius, 2px stroke, #06B6D4 (cyan-500), 60% opacity
- **Ring 3 (outer):** 360px radius, 2px stroke, #22D3EE (cyan-400), 40% opacity
- **Orbit labels:** 3 text labels orbiting at Ring 3 radius, 18px Inter, #94A3B8
- **Radial lines:** 8 faint lines from center to Ring 3, #1E293B, 1px

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Central dot fades in and begins pulse animation (scale 1.0-1.3 loop)
2. **Frame 10-30 (0.33-1.0s):** Ring 1 expands from radius 0 to 120px with opacity fade-in
3. **Frame 20-45 (0.67-1.5s):** Ring 2 expands from radius 0 to 240px with opacity fade-in
4. **Frame 30-55 (1.0-1.83s):** Ring 3 expands from radius 0 to 360px with opacity fade-in
5. **Frame 40-75 (1.33-2.5s):** Orbit labels fade in and begin rotating at 0.5 deg/frame
6. **Frame 0-75 (continuous):** Radial lines at 15% opacity, static

### Typography
- Orbit labels: Inter, 18px, normal, #94A3B8
- No title text on this component (overlay from title card)

### Easing
- Ring expansion: `easeOutQuart`
- Central dot pulse: `easeInOutSine` (looping)
- Label fade: `easeOutCubic`

## Narration Sync
> "This is the first section of the integration test video."

Overlaps with the title card during Segment 1 (0.0s-2.9s). The pulse visualization reinforces the "first section" concept with an opening visual motif.

## Code Structure (Remotion)
```typescript
<Sequence from={30} durationInFrames={75}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    <RadialLines count={8} maxRadius={360} color="#1E293B" />
    <PulsingDot cx={960} cy={540} color="#60A5FA" />
    <Sequence from={10}>
      <ExpandingRing radius={120} stroke="#3B82F6" opacity={0.8} />
    </Sequence>
    <Sequence from={20}>
      <ExpandingRing radius={240} stroke="#06B6D4" opacity={0.6} />
    </Sequence>
    <Sequence from={30}>
      <ExpandingRing radius={360} stroke="#22D3EE" opacity={0.4} />
    </Sequence>
    <Sequence from={40}>
      <OrbitLabels labels={["Section 1", "Remotion", "30fps"]} radius={360} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "rings": [
    { "radius": 120, "color": "#3B82F6", "opacity": 0.8 },
    { "radius": 240, "color": "#06B6D4", "opacity": 0.6 },
    { "radius": 360, "color": "#22D3EE", "opacity": 0.4 }
  ],
  "labels": ["Section 1", "Remotion", "30fps"]
}
```

---
