[Remotion]

# Section 0.6: "Why Are We Still Patching?" — Rhetorical Beat

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:55 - 1:05

## Visual Description
A data-driven visual reinforcement of the rhetorical question. The clean regenerated code from the previous scene fades to background (30% opacity, blurred), and three concentric rings animate outward from center — each representing a key statistic about the futility of patching. The rings expand and settle, with stat callouts appearing at each ring's edge. This transforms the emotional gut-punch of the previous scene into concrete data, setting up the analytical tone of the rest of the video.

The visual echoes the 3Blue1Brown style: geometric, mathematical, and revelatory.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep blue-black `#0B1120` with faint code texture at 5% opacity (remnant of previous scene)
- Grid lines: None

### Chart/Visual Elements
- **Center Point:** Small glowing circle `#4A90D9`, 8px radius, at (960, 540) — the "patch" origin
- **Ring 1 (innermost):** Radius 120px, stroke `#D9944A` (amber/patch color), 2px stroke, dashed
  - Stat callout at 2 o'clock position: "+44% code churn"
- **Ring 2 (middle):** Radius 220px, stroke `#EF4444` (red/debt color), 2px stroke, dashed
  - Stat callout at 10 o'clock position: "41% more bugs"
- **Ring 3 (outermost):** Radius 340px, stroke `#F59E0B` (warning yellow), 2px stroke, dashed
  - Stat callout at 5 o'clock position: "-60% refactoring"
- **Stat Callouts:** Small filled circle (10px) at ring edge + horizontal leader line (40px) + stat text
- **Center Label:** "each patch" in `#94A3B8`, 18px, directly below center point

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Previous scene blurs and fades to 5% opacity background texture. Dark background takes over.
2. **Frame 20-40 (0.67-1.33s):** Center point appears — small blue glow pulses once. "each patch" label fades in below.
3. **Frame 40-80 (1.33-2.67s):** Ring 1 draws outward from center (stroke-dashoffset animation), expanding to 120px radius. Once settled, stat callout "+44% code churn" fades in at 2 o'clock with leader line.
4. **Frame 80-130 (2.67-4.33s):** Ring 2 draws outward from center to 220px. Stat callout "41% more bugs" fades in at 10 o'clock.
5. **Frame 130-180 (4.33-6.0s):** Ring 3 draws outward from center to 340px. Stat callout "-60% refactoring" fades in at 5 o'clock.
6. **Frame 180-220 (6.0-7.33s):** All three rings pulse once simultaneously (scale 1.0→1.03→1.0), reinforcing the concentric impact.
7. **Frame 220-300 (7.33-10.0s):** Hold. Subtle ambient glow on center point breathes slowly (opacity 0.6→0.8→0.6, 60-frame cycle).

### Typography
- Stat values: Inter, 28px, bold (700), white `#FFFFFF`
- Stat descriptions: Inter, 18px, regular (400), `#94A3B8`
- Center label "each patch": Inter, 18px, italic, `#94A3B8`
- Source citations: Inter, 11px, `#64748B`, positioned 20px below each stat

### Easing
- Ring draw: `easeOut(cubic)` — expands quickly then settles
- Stat callout fade: `easeOut(quad)`
- Leader line extend: `easeOut(quad)`
- Concentric pulse: `easeInOut(sin)`
- Background blur transition: `easeIn(quad)`

## Narration Sync
> "So why are we still patching?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Background fade from previous scene */}
  <BlurFade toOpacity={0.05} durationInFrames={20} />

  <AbsoluteFill style={{ backgroundColor: '#0B1120' }}>
    {/* Center Origin */}
    <Sequence from={20}>
      <GlowDot center={[960, 540]} radius={8} color="#4A90D9" />
      <FadeIn durationInFrames={15}>
        <Label text="each patch" position={[960, 570]} color="#94A3B8" />
      </FadeIn>
    </Sequence>

    {/* Ring 1: Code Churn */}
    <Sequence from={40}>
      <ExpandingRing
        center={[960, 540]}
        radius={120}
        strokeColor="#D9944A"
        durationInFrames={30}
      />
      <Sequence from={30}>
        <StatCallout
          angle={60}
          radius={120}
          value="+44%"
          label="code churn"
          source="GitClear, 2025"
        />
      </Sequence>
    </Sequence>

    {/* Ring 2: More Bugs */}
    <Sequence from={80}>
      <ExpandingRing center={[960, 540]} radius={220} strokeColor="#EF4444" durationInFrames={35} />
      <Sequence from={35}>
        <StatCallout angle={300} radius={220} value="41%" label="more bugs" source="Uplevel, 2024" />
      </Sequence>
    </Sequence>

    {/* Ring 3: Refactoring Decline */}
    <Sequence from={130}>
      <ExpandingRing center={[960, 540]} radius={340} strokeColor="#F59E0B" durationInFrames={35} />
      <Sequence from={35}>
        <StatCallout angle={150} radius={340} value="-60%" label="refactoring" source="GitClear, 2025" />
      </Sequence>
    </Sequence>

    {/* Concentric Pulse */}
    <Sequence from={180}>
      <ConcentricPulse rings={[120, 220, 340]} scale={1.03} durationInFrames={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "center": [960, 540],
  "rings": [
    {
      "radius": 120,
      "strokeColor": "#D9944A",
      "stat": { "value": "+44%", "label": "code churn", "source": "GitClear, 2025" },
      "calloutAngle": 60
    },
    {
      "radius": 220,
      "strokeColor": "#EF4444",
      "stat": { "value": "41%", "label": "more bugs", "source": "Uplevel, 2024" },
      "calloutAngle": 300
    },
    {
      "radius": 340,
      "strokeColor": "#F59E0B",
      "stat": { "value": "-60%", "label": "refactoring", "source": "GitClear, 2025" },
      "calloutAngle": 150
    }
  ],
  "centerDot": {
    "color": "#4A90D9",
    "radius": 8
  },
  "backgroundColor": "#0B1120"
}
```

---
