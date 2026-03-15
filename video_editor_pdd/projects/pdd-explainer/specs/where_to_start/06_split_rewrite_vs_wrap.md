[split:]

# Section 6.6: Split — Full Rewrite vs. Gradual Adoption

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 23:18 - 23:32

## Visual Description
A split-screen comparison addressing the viewer's biggest fear: "Do I have to rewrite everything?" The LEFT side shows "Big Bang Rewrite" — a dramatic, risky approach where an entire codebase is replaced at once, depicted as a wrecking ball swinging into a building. The building shatters and a new one appears, but with visible cracks and a red "HIGH RISK" badge. The RIGHT side shows "Module-by-Module" — the PDD gradual adoption path, depicted as individual bricks in a wall being swapped out one at a time while the structure stays standing. Each swapped brick glows blue briefly, then settles in. A progress bar shows 4/20 modules converted. Below, a clear verdict: "You don't rewrite. You replace one brick at a time."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, Y: 60-900, `rgba(255,255,255,0.12)`
- **LEFT Panel (X: 40-940) — Big Bang Rewrite:**
  - Header: "Big Bang Rewrite" — Inter 24px bold, `#EF4444` at 0.8, centered at X=490, Y=70
  - Building (pre-destruction): Stylized rectangle grid (5 cols x 8 rows of "bricks"), 400px wide x 360px tall, centered at X=490, Y=300. Bricks `rgba(255,255,255,0.1)`, 1px gap between
  - Wrecking ball: Circle 60px, `#EF4444` at 0.4, connected by line to top-right, swings from right
  - Shatter effect: Bricks scatter outward with physics-like trajectories (rotation + translation)
  - New building (post-rebuild): Same 5x8 grid but with 3 bricks misaligned/cracked, `rgba(255,255,255,0.08)`. Red cracks: `#EF4444` at 0.2
  - Risk badge: Rounded rect 140px x 36px, `rgba(239,68,68,0.15)` fill, border `#EF4444` at 0.4. Text "HIGH RISK" — Inter 14px bold, `#EF4444`. Positioned at X=490, Y=680
  - Subtitle: "All or nothing. Months of work. Pray it works." — Inter 14px, `#94A3B8`, Y=740
- **RIGHT Panel (X: 980-1880) — Module-by-Module:**
  - Header: "Module by Module" — Inter 24px bold, `#4A90D9` at 0.8, centered at X=1430, Y=70
  - Wall (persistent structure): Same 5 cols x 8 rows brick grid, 400px wide x 360px tall, centered at X=1430, Y=300. Bricks `rgba(255,255,255,0.1)` initially
  - Swap animation: Individual bricks (4 specific ones) get replaced — old brick slides out right, new brick slides in from left with blue glow `#4A90D9` at 0.3, then settles to `rgba(74,144,217,0.15)`
  - Swapped bricks have a subtle inner glow to distinguish them
  - Wall structure remains perfectly intact throughout
  - Progress bar: 600px wide x 8px tall, centered at X=1430, Y=680
    - Track: `rgba(255,255,255,0.08)`
    - Fill: `#4A90D9`, width proportional to 4/20 (120px)
    - Label: "4 of 20 modules" — Inter 13px, `#4A90D9`, right-aligned at bar end
  - Safety badge: Rounded rect 140px x 36px, `rgba(74,144,217,0.12)` fill, border `#4A90D9` at 0.3. Text "LOW RISK" — Inter 14px bold, `#4A90D9`. Positioned at X=1430, Y=720
  - Subtitle: "One module at a time. Tests pass before you move on." — Inter 14px, `#94A3B8`, Y=760
- **Bottom Verdict (centered, Y=880):**
  - "You don't rewrite. You replace one brick at a time." — Inter 22px semi-bold, `#FFFFFF` at 0.7

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider fades in. Both headers appear simultaneously
2. **Frame 20-60 (0.67-2.0s):** Both building/wall structures draw in — bricks appear row-by-row from bottom (8-frame stagger per row)
3. **Frame 60-140 (2.0-4.67s):** LEFT: Wrecking ball swings in from right. On impact (Frame 100), bricks scatter with physics animation — each brick gets random velocity, rotation, and gravity. Dramatic, chaotic
4. **Frame 140-200 (4.67-6.67s):** LEFT: Scattered bricks fade out. New building materializes in place (fade in 0→1) but with visible cracks and misalignments. Risk badge fades in below
5. **Frame 80-280 (2.67-9.33s):** RIGHT (overlapping with left): Four bricks get swapped sequentially with 40-frame stagger:
   - Brick at row 2, col 3 → slides out, new blue brick slides in
   - Brick at row 4, col 1 → slides out, new blue brick slides in
   - Brick at row 6, col 5 → slides out, new blue brick slides in
   - Brick at row 7, col 2 → slides out, new blue brick slides in
   - Each swap: old brick slides right (20px) and fades, new brick slides in from left with blue glow, settles
6. **Frame 280-320 (9.33-10.67s):** RIGHT: Progress bar fills to 4/20. "4 of 20 modules" label appears. Safety badge fades in
7. **Frame 320-360 (10.67-12.0s):** Both subtitles fade in. LEFT panel gets a subtle red vignette `rgba(239,68,68,0.03)`. RIGHT panel gets a subtle blue vignette `rgba(74,144,217,0.03)`
8. **Frame 360-390 (12.0-13.0s):** Bottom verdict text fades in centered
9. **Frame 390-420 (13.0-14.0s):** Hold. Right panel's swapped bricks pulse gently

### Typography
- Headers: Inter, 24px, bold (700), respective colors at 0.8 opacity
- Risk/Safety Badges: Inter, 14px, bold (700), respective colors
- Subtitles: Inter, 14px, regular (400), `#94A3B8`
- Progress Label: Inter, 13px, medium (500), `#4A90D9`
- Bottom Verdict: Inter, 22px, semi-bold (600), `#FFFFFF` at 0.7

### Easing
- Brick row appear: `easeOut(quad)`
- Wrecking ball swing: `easeIn(quad)` (accelerating into impact)
- Brick scatter: `easeOut(quad)` with gravity (quadratic Y deceleration)
- New building fade: `easeOut(quad)`
- Brick swap slide: `easeInOut(cubic)`
- Blue glow: `easeOut(quad)` in, `easeIn(quad)` settle
- Progress bar fill: `easeOut(cubic)`
- Verdict text fade: `easeOut(quad)`

## Narration Sync
> "And here's the thing people get wrong: PDD is not a rewrite. You do not throw away your codebase and start over. You convert one module at a time. Pick a leaf. Write the prompt. Link the tests. Generate. If the tests pass, that module is now PDD-managed. Everything else stays exactly the same. Four modules. Then ten. Then twenty. No big bang. No all-or-nothing bet."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Divider and Headers */}
  <Sequence from={0} durationInFrames={20}>
    <VerticalDivider x={960} />
    <SplitHeaders left="Big Bang Rewrite" right="Module by Module" leftColor="#EF4444" rightColor="#4A90D9" />
  </Sequence>

  {/* Both Walls Build */}
  <Sequence from={20} durationInFrames={40}>
    <BrickGrid x={490} y={300} cols={5} rows={8} panel="left" />
    <BrickGrid x={1430} y={300} cols={5} rows={8} panel="right" />
  </Sequence>

  {/* LEFT: Wrecking Ball */}
  <Sequence from={60} durationInFrames={80}>
    <WreckingBall
      targetX={490} targetY={300}
      impactFrame={40}
      ballSize={60}
      color="#EF4444"
    />
    <BrickScatter startFrame={40} brickCount={40} />
  </Sequence>

  {/* LEFT: Rebuilt (with cracks) */}
  <Sequence from={140} durationInFrames={60}>
    <CrackedBuildingFade x={490} y={300} crackColor="#EF4444" />
    <RiskBadge text="HIGH RISK" color="#EF4444" y={680} />
  </Sequence>

  {/* RIGHT: Brick Swaps */}
  {swapTargets.map((brick, i) => (
    <Sequence key={brick.id} from={80 + i * 40} durationInFrames={40}>
      <BrickSwap
        row={brick.row} col={brick.col}
        newColor="rgba(74,144,217,0.15)"
        glowColor="#4A90D9"
      />
    </Sequence>
  ))}

  {/* RIGHT: Progress Bar */}
  <Sequence from={280} durationInFrames={40}>
    <ProgressBar
      current={4} total={20}
      width={600} y={680}
      color="#4A90D9"
    />
    <SafetyBadge text="LOW RISK" color="#4A90D9" y={720} />
  </Sequence>

  {/* Bottom Verdict */}
  <Sequence from={360} durationInFrames={30}>
    <FadeText
      text="You don't rewrite. You replace one brick at a time."
      fontSize={22}
      opacity={0.7}
      y={880}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "dividerColor": "rgba(255,255,255,0.12)",
  "leftPanel": {
    "header": "Big Bang Rewrite",
    "headerColor": "#EF4444",
    "grid": { "cols": 5, "rows": 8 },
    "riskBadge": "HIGH RISK",
    "subtitle": "All or nothing. Months of work. Pray it works."
  },
  "rightPanel": {
    "header": "Module by Module",
    "headerColor": "#4A90D9",
    "grid": { "cols": 5, "rows": 8 },
    "swapTargets": [
      { "row": 2, "col": 3 },
      { "row": 4, "col": 1 },
      { "row": 6, "col": 5 },
      { "row": 7, "col": 2 }
    ],
    "progress": { "current": 4, "total": 20 },
    "safetyBadge": "LOW RISK",
    "subtitle": "One module at a time. Tests pass before you move on."
  },
  "verdict": "You don't rewrite. You replace one brick at a time."
}
```

---
