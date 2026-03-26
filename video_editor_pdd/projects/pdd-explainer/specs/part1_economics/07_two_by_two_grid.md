[Remotion]

# Section 1.7: Two-by-Two Grid — Reconciling Conflicting Studies

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 3:56 - 4:18

## Visual Description

A clean 2×2 quadrant grid that resolves the "AI helps / AI hurts" contradiction. This is the "aha" moment where conflicting research makes sense.

X-axis runs from "Greenfield" (left) to "Brownfield" (right). Y-axis runs from "In-Distribution" (bottom) to "Out-of-Distribution" (top).

The quadrants light up sequentially:
- **Top-Left (Greenfield + In-Distribution):** Glows green. "GitHub study: +55%". This is where AI shines — new code, within its training data.
- **Bottom-Right (Brownfield + Out-of-Distribution):** Glows red. "METR study: −19%". This is where AI struggles — mature repos, novel problems.
- **Top-Right and Bottom-Left:** Intermediate amber, no specific data.

A clean label ties it together: "Every study is correct. They just measured different quadrants."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none (the quadrant borders are the structure)

### Chart/Visual Elements

#### Quadrant Frame
- Total grid: 680×680px, centered at (960, 480)
- Quadrant borders: 2px, `#334155` at 0.4
- Each quadrant: 340×340px

#### Axis Labels
- X-axis: "Greenfield" (left) ↔ "Brownfield" (right)
  - Inter, 14px, bold, `#94A3B8` at 0.6, positioned below grid
  - Arrow: thin `#94A3B8` at 0.2 connecting the two labels
- Y-axis: "In-Distribution" (bottom) ↔ "Out-of-Distribution" (top)
  - Inter, 14px, bold, `#94A3B8` at 0.6, positioned left of grid, rotated -90°
  - Arrow: thin `#94A3B8` at 0.2 connecting the two labels

#### Quadrants
- **Top-Left (Greenfield + In-Dist):**
  - Fill: `#22C55E` at 0.12, border glow `#22C55E` at 0.3
  - Label: "GitHub study:" — Inter, 14px, `#22C55E`
  - Value: "+55%" — Inter, 28px, bold, `#22C55E`
- **Bottom-Right (Brownfield + Out-of-Dist):**
  - Fill: `#EF4444` at 0.12, border glow `#EF4444` at 0.3
  - Label: "METR study:" — Inter, 14px, `#EF4444`
  - Value: "−19%" — Inter, 28px, bold, `#EF4444`
- **Top-Right (Brownfield + In-Dist):**
  - Fill: `#F59E0B` at 0.06
  - No specific data label
- **Bottom-Left (Greenfield + Out-of-Dist):**
  - Fill: `#F59E0B` at 0.06
  - No specific data label

#### Summary Label
- "Every study is correct. They just measured different quadrants."
  - Inter, 16px, `#E2E8F0` at 0.7
  - Centered below the grid at y: 880

### Animation Sequence
1. **Frame 0-60 (0-2s):** Quadrant frame draws in. Borders appear. Axis labels fade in.
2. **Frame 60-180 (2-6s):** Top-left quadrant fills green. "GitHub study: +55%" appears.
3. **Frame 180-360 (6-12s):** Bottom-right quadrant fills red. "METR study: −19%" appears. The contrast is stark.
4. **Frame 360-420 (12-14s):** Intermediate quadrants fill with faint amber.
5. **Frame 420-540 (14-18s):** Summary label fades in below the grid.
6. **Frame 540-660 (18-22s):** Hold. The visual explanation settles. Both quadrants pulse gently.

### Typography
- Axis labels: Inter, 14px, bold (700), `#94A3B8` at 0.6
- Quadrant study labels: Inter, 14px, respective colors
- Quadrant values: Inter, 28px, bold (700), respective colors
- Summary: Inter, 16px, `#E2E8F0` at 0.7

### Easing
- Frame draw: `easeOut(cubic)` over 30 frames
- Quadrant fill: `easeOut(quad)` over 30 frames — bloom from center
- Text appear: `easeOut(quad)` over 20 frames
- Quadrant pulse: `easeInOut(sine)` on 90-frame cycle, subtle opacity shift ±0.03
- Summary: `easeOut(quad)` over 25 frames

## Narration Sync
> "GitHub study measured greenfield in-distribution tasks... METR measured brownfield out-of-distribution tasks..."
> "Small codebase. A few thousand lines. Clean modules. Well-documented."
> "on a large codebase, the same developer with the same tools was 19% slower..."

Segments: `part1_economics_023`, `part1_economics_024`, `part1_economics_025`

- **255.58s** ("GitHub study measured greenfield"): Top-left quadrant lights up green
- **268s** ("METR measured brownfield"): Bottom-right lights up red
- **277.54s** ("Small codebase"): Summary label appearing
- **289.06s** ("on a large codebase"): Both quadrants visible, contrast clear

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Quadrant frame */}
    <Sequence from={0}>
      <StrokeDraw duration={30}>
        <QuadrantFrame
          center={[960, 480]} size={680}
          borderColor="#334155" borderOpacity={0.4} borderWidth={2} />
      </StrokeDraw>
    </Sequence>

    {/* Axis labels */}
    <Sequence from={30}>
      <FadeIn duration={20}>
        <AxisLabel text="Greenfield" x={620} y={850} color="#94A3B8" />
        <AxisLabel text="Brownfield" x={1300} y={850} color="#94A3B8" />
        <AxisLabel text="In-Distribution" x={560} y={660} color="#94A3B8" rotate={-90} />
        <AxisLabel text="Out-of-Distribution" x={560} y={300} color="#94A3B8" rotate={-90} />
      </FadeIn>
    </Sequence>

    {/* Top-left: Greenfield + In-Dist = GitHub +55% */}
    <Sequence from={60}>
      <QuadrantFill position="top-left" color="#22C55E" opacity={0.12}
        glowOpacity={0.3} fillDuration={30}>
        <Sequence from={30}>
          <FadeIn duration={20}>
            <Text text="GitHub study:" font="Inter" size={14} color="#22C55E" />
            <Text text="+55%" font="Inter" size={28} weight={700} color="#22C55E" />
          </FadeIn>
        </Sequence>
      </QuadrantFill>
    </Sequence>

    {/* Bottom-right: Brownfield + Out-of-Dist = METR -19% */}
    <Sequence from={180}>
      <QuadrantFill position="bottom-right" color="#EF4444" opacity={0.12}
        glowOpacity={0.3} fillDuration={30}>
        <Sequence from={30}>
          <FadeIn duration={20}>
            <Text text="METR study:" font="Inter" size={14} color="#EF4444" />
            <Text text="−19%" font="Inter" size={28} weight={700} color="#EF4444" />
          </FadeIn>
        </Sequence>
      </QuadrantFill>
    </Sequence>

    {/* Intermediate quadrants */}
    <Sequence from={360}>
      <QuadrantFill position="top-right" color="#F59E0B" opacity={0.06} fillDuration={20} />
      <QuadrantFill position="bottom-left" color="#F59E0B" opacity={0.06} fillDuration={20} />
    </Sequence>

    {/* Summary label */}
    <Sequence from={420}>
      <FadeIn duration={25}>
        <Text
          text="Every study is correct. They just measured different quadrants."
          font="Inter" size={16} color="#E2E8F0" opacity={0.7}
          x={960} y={880} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "two_by_two_grid",
  "axes": {
    "x": { "left": "Greenfield", "right": "Brownfield" },
    "y": { "bottom": "In-Distribution", "top": "Out-of-Distribution" }
  },
  "quadrants": [
    {
      "position": "top-left",
      "label": "GitHub study",
      "value": "+55%",
      "color": "#22C55E",
      "interpretation": "greenfield_in_distribution"
    },
    {
      "position": "bottom-right",
      "label": "METR study",
      "value": "−19%",
      "color": "#EF4444",
      "interpretation": "brownfield_out_of_distribution"
    },
    { "position": "top-right", "color": "#F59E0B", "interpretation": "intermediate" },
    { "position": "bottom-left", "color": "#F59E0B", "interpretation": "intermediate" }
  ],
  "summary": "Every study is correct. They just measured different quadrants.",
  "narrationSegments": ["part1_economics_023", "part1_economics_024", "part1_economics_025"]
}
```

---
