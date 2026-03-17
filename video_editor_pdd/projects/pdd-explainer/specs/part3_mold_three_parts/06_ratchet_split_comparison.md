[split:]

# Section 3.6: Ratchet Split Comparison — Traditional vs PDD Bug Workflow

**Tool:** Split
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 13:49 - 14:05

## Visual Description

A vertical split screen contrasts two bug-fixing workflows. LEFT panel (labeled "TRADITIONAL") shows the familiar, frustrating cycle: Bug found → Patch code → Similar bug elsewhere → Patch again → Different bug → Patch again. Each iteration is a new row that scrolls downward, growing into an endless list. Red X marks accumulate. The visual impression is Sisyphean — the work never ends.

RIGHT panel (labeled "PDD") shows the mold-based workflow: Bug found → Add test wall (`pdd bug`) → Regenerate (`pdd fix`) → Bug impossible forever. Only three rows. The last row glows green with a permanent checkmark. A small mold icon shows a new wall being added, and the shape tightening.

Below the split, a timeline bar shows "OVER TIME" — the left side shows patching effort growing linearly (red line rising), while the right side shows test accumulation as a ratchet (green staircase that only goes up). The ratchet metaphor is visually clear: each step is permanent, each wall stays.

A key callout appears at bottom: "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "TRADITIONAL" — Inter, 14px, semi-bold (600), `#EF4444` at 0.5, letter-spacing 2px, centered at y: 40
- RIGHT: "PDD" — Inter, 14px, semi-bold (600), `#5AAA6E` at 0.5, letter-spacing 2px, centered at y: 40

#### Left Panel — Traditional Patching (x: 0 to x: 958)
- Background: `#0F172A`
- **Row format:** Each row is 60px tall with:
  - Status icon: red X (`#EF4444`) or amber warning (`#D9944A`), 16px
  - Action text: JetBrains Mono, 12px, `#94A3B8`
  - Result text: JetBrains Mono, 10px, `#64748B` at 0.5
- **Rows (scrolling):**
  1. "Bug found: null crash" → "Patch: add null check" → ✗
  2. "Same bug: different module" → "Patch: add null check" → ✗
  3. "New bug: unicode failure" → "Patch: encode input" → ✗
  4. "Regression: null check broke edge case" → "Patch: add condition" → ✗
  5. "Performance bug: O(n²)" → "Patch: optimize loop" → ✗
  6. (rows continue scrolling, 8+ total, increasingly overwhelming)
- **Effort counter:** bottom of panel, "Patches: N" incrementing, Inter, 16px, `#EF4444`

#### Right Panel — PDD (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **Row format:** Same height, cleaner layout
- **Rows (only 3):**
  1. "Bug found: null crash" → icon: red alert
  2. "`pdd bug user_parser`" → icon: amber wall being added, terminal text
  3. "`pdd fix user_parser` → All tests pass ✓" → icon: green checkmark, glowing
- **Subtitle:** "Bug impossible forever" — Inter, 14px, bold (700), `#5AAA6E` at 0.8, with infinity symbol ∞
- **Mini mold icon:** 80×100px mold cross-section showing a new wall added, `#D9944A` at 0.4

#### Timeline Bar (bottom, y: 820-920)
- LEFT: Red line (`#EF4444` at 0.5, 2px) rising linearly from left to right, label "Patching effort" at end
- RIGHT: Green staircase (`#5AAA6E` at 0.5, 2px) — each step is a wall added, ratchet only goes up, label "Test accumulation" at end
- X-axis: "TIME →" — Inter, 10px, `#64748B` at 0.3
- Ratchet teeth: small triangular notches on each step, `#5AAA6E` at 0.3, showing irreversibility

#### Callout Text (bottom center, y: 970)
- "A bug fix helps one place. A test prevents that bug everywhere, forever." — Inter, 14px, `#E2E8F0` at 0.7
- "everywhere, forever" in bold, `#5AAA6E`

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-60 (0.67-2s):** LEFT: First row appears — bug found, patch applied, red X. RIGHT: First row — bug found, red alert.
3. **Frame 60-120 (2-4s):** LEFT: Rows 2-3 appear, scrolling. More patches, more X marks. Effort counter increments. RIGHT: Row 2 — `pdd bug` command, wall being added (amber glow).
4. **Frame 120-200 (4-6.67s):** LEFT: Rows 4-6 scroll in. The panel is getting crowded. Counter rising. RIGHT: Row 3 — `pdd fix`, green checkmark glows. "Bug impossible forever" text appears with ∞.
5. **Frame 200-280 (6.67-9.33s):** LEFT: Rows 7-8 still scrolling. Visually overwhelming. RIGHT: Mini mold icon appears showing the tightened shape. Clean, resolved.
6. **Frame 280-380 (9.33-12.67s):** Timeline bar appears at bottom. LEFT red line draws rising. RIGHT green staircase draws with ratchet teeth. The contrast is stark.
7. **Frame 380-420 (12.67-14s):** Callout text fades in at bottom. "everywhere, forever" pulses green.
8. **Frame 420-480 (14-16s):** Hold on complete picture. Left panel still slowly scrolling (patches never end). Right panel static and resolved.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- Row action text: JetBrains Mono, 12px, `#94A3B8`
- Row result text: JetBrains Mono, 10px, `#64748B` at 0.5
- Effort counter: Inter, 16px, `#EF4444`
- PDD subtitle: Inter, 14px, bold (700), `#5AAA6E` at 0.8
- Callout: Inter, 14px, `#E2E8F0` at 0.7, bold on "everywhere, forever"

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Row appear: `easeOut(quad)` from x-20, 15 frames each
- Left scroll: `linear`, continuous after frame 200
- Green checkmark: `spring({ stiffness: 180, damping: 10 })` scale from 0
- Timeline line draw: `easeInOut(cubic)` over 60 frames
- Ratchet step: `easeOut(quad)` over 8 frames per step
- Callout fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."
> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

Segment: `part3_006`

- **13:49** ("This is the ratchet effect"): Split screen appears, both panels begin
- **13:53** ("Tests only accumulate"): PDD side shows wall being added, traditional side scrolling
- **13:57** ("Each wall you add constrains all future generations"): Timeline bar with ratchet staircase
- **14:01** ("a bug fix helps one place"): Left panel overwhelmed, right resolved
- **14:03** ("a test prevents that bug everywhere, forever"): Callout text, green pulse

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Traditional */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="TRADITIONAL" color="#EF4444"
          opacity={0.5} letterSpacing={2} y={40} />

        <ScrollingRows rows={traditionalRows}
          rowHeight={60} font="JetBrains Mono"
          iconColor="#EF4444" textColor="#94A3B8"
          autoScrollAfter={200} scrollSpeed={0.5} />

        <EffortCounter label="Patches:" color="#EF4444"
          font="Inter" size={16} position={[480, 780]}
          incrementTriggers={rowAppearFrames} />
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.25}
      drawDuration={15} />

    {/* Right panel — PDD */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="PDD" color="#5AAA6E"
          opacity={0.5} letterSpacing={2} y={40} />

        <StaticRows rows={pddRows} rowHeight={60}
          font="JetBrains Mono" stagger={60} />

        <Sequence from={120}>
          <SpringScale stiffness={180} damping={10}>
            <Text text="Bug impossible forever ∞"
              font="Inter" size={14} weight={700}
              color="#5AAA6E" opacity={0.8}
              x={480} y={340} align="center" />
          </SpringScale>
        </Sequence>

        <Sequence from={200}>
          <MiniMold position={[480, 500]} size={[80, 100]}
            wallColor="#D9944A" opacity={0.4}
            newWall={{ position: 'left', label: 'null check' }} />
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Timeline bar */}
    <Sequence from={280}>
      <TimelineBar y={870} width={1800}
        left={{ type: 'rising_line', color: '#EF4444', label: 'Patching effort' }}
        right={{ type: 'ratchet_staircase', color: '#5AAA6E',
          label: 'Test accumulation', teeth: true }}
        xLabel="TIME →" drawDuration={60}
      />
    </Sequence>

    {/* Callout text */}
    <Sequence from={380}>
      <FadeIn duration={20}>
        <RichText x={960} y={970} align="center" font="Inter" size={14}
          color="#E2E8F0" opacity={0.7}>
          A bug fix helps one place. A test prevents that bug{' '}
          <Bold color="#5AAA6E">everywhere, forever</Bold>.
        </RichText>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "label": "TRADITIONAL",
    "concept": "Bug → Patch → Repeat forever",
    "rows": [
      "Bug: null crash → Patch: add null check",
      "Same bug: different module → Patch again",
      "New bug: unicode → Patch: encode input",
      "Regression → Patch: add condition",
      "Performance bug → Patch: optimize",
      "Another null crash → Patch again..."
    ],
    "background": "#0F172A",
    "statusColor": "#EF4444"
  },
  "rightPanel": {
    "label": "PDD",
    "concept": "Bug → Add wall → Regenerate → Bug impossible forever",
    "rows": [
      "Bug found: null crash",
      "pdd bug user_parser → test wall added",
      "pdd fix user_parser → All tests pass ✓"
    ],
    "background": "#0A0F1A",
    "statusColor": "#5AAA6E"
  },
  "timelineBar": {
    "left": { "type": "rising_line", "label": "Patching effort" },
    "right": { "type": "ratchet_staircase", "label": "Test accumulation" }
  },
  "callout": "A bug fix helps one place. A test prevents that bug everywhere, forever.",
  "backgroundColor": "#000000",
  "narrationSegments": ["part3_006"]
}
```

---
