[split:]

# Section 1.6: Framework Comparison — Remotion vs. Veo

**Tool:** Remotion
**Duration:** ~2s (60 frames)
**Timestamp:** 0:04 - 0:06

## Visual Description
A split-screen comparison showing the two rendering approaches side by side. The left half is labeled "Remotion" on a deep blue background (#1E3A8A) with a miniature animated bar chart (mirroring the key visual). The right half is labeled "Veo" on a dark slate background (#334155) with a film-reel icon and the text "AI-Generated." A thin vertical divider separates the halves. Each side fades in independently, left first, then right, emphasizing that this section focuses on the Remotion side.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Split — left half #1E3A8A, right half #334155
- Vertical divider: 2px wide, color #94A3B8, centered at x=960

### Chart/Visual Elements
- **Left panel (Remotion):**
  - Background: #1E3A8A
  - Label: "Remotion" at (240, 200), color #FFFFFF, 48px, bold
  - Sub-label: "Deterministic Rendering" at (240, 260), color #93C5FD, 24px, normal
  - Mini bar chart: 4 bars (60px wide, gap 16px), colors alternating #38BDF8 / #22C55E, positioned at center-bottom of left half
  - Glow border: Left panel has a 2px inner border glow, color #3B82F6 at 40% opacity

- **Right panel (Veo):**
  - Background: #334155
  - Label: "Veo" at (1200, 200), color #FFFFFF, 48px, bold
  - Sub-label: "AI-Generated Footage" at (1200, 260), color #CBD5E1, 24px, normal
  - Film reel icon: Centered in right panel, 120x120px, color #64748B at 30% opacity
  - Dimmed state: Right panel has 60% overall opacity (de-emphasized for this section)

- **Divider line:** Vertical, 2px, x=960, full height, color #94A3B8

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Left panel fades in (opacity 0→1), label slides down from y=180→y=200
2. **Frame 5-25 (0.17-0.83s):** Mini bar chart bars grow upward (staggered, 5-frame delay each)
3. **Frame 15-35 (0.5-1.17s):** Divider line draws top-to-bottom
4. **Frame 25-45 (0.83-1.5s):** Right panel fades in to 60% opacity, label slides down from y=180→y=200
5. **Frame 40-60 (1.33-2.0s):** Left panel glow border pulses once (opacity 0.2→0.6→0.2)

### Typography
- Panel labels: Inter, 48px, bold (700), #FFFFFF
- Sub-labels: Inter, 24px, normal (400), #93C5FD (left) / #CBD5E1 (right)

### Easing
- Panel fade-in: `easeOutQuad`
- Label slide: `easeOutCubic`
- Mini bar growth: `easeOutQuad`
- Divider draw: `linear`
- Glow pulse: `easeInOutSine`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

The split view appears during segment 2 (4.0s-6.0s), visually contrasting the two pipeline modes. The left (Remotion) panel is emphasized and glowing while the right (Veo) panel is dimmed — reinforcing the narration that this section is Remotion-only.

## Code Structure (Remotion)
```typescript
<Sequence from={120} durationInFrames={60}>
  <AbsoluteFill style={{ display: 'flex' }}>
    {/* Left panel — Remotion */}
    <Sequence from={0} durationInFrames={20}>
      <SplitPanel
        side="left"
        backgroundColor="#1E3A8A"
        label="Remotion"
        subLabel="Deterministic Rendering"
        opacity={1}
      >
        <MiniBarChart bars={[0.35, 0.55, 0.8, 0.6]} />
      </SplitPanel>
    </Sequence>

    {/* Divider */}
    <Sequence from={15} durationInFrames={20}>
      <VerticalDivider x={960} color="#94A3B8" />
    </Sequence>

    {/* Right panel — Veo */}
    <Sequence from={25} durationInFrames={20}>
      <SplitPanel
        side="right"
        backgroundColor="#334155"
        label="Veo"
        subLabel="AI-Generated Footage"
        opacity={0.6}
      >
        <FilmReelIcon size={120} color="#64748B" />
      </SplitPanel>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "panels": [
    {
      "side": "left",
      "label": "Remotion",
      "subLabel": "Deterministic Rendering",
      "backgroundColor": "#1E3A8A",
      "emphasis": true,
      "opacity": 1.0
    },
    {
      "side": "right",
      "label": "Veo",
      "subLabel": "AI-Generated Footage",
      "backgroundColor": "#334155",
      "emphasis": false,
      "opacity": 0.6
    }
  ],
  "dividerColor": "#94A3B8"
}
```

---
