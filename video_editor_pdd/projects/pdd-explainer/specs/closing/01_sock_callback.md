[split:]

# Section 7.1: Sock Callback — The Final Discard

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 24:15 - 24:23

## Visual Description
The sock metaphor returns one final time — stripped to its essence. A split-screen shows a holey sock on the left and a buggy code file on the right, both rendered as minimal silhouettes against the dark background. A figure on each side considers the object briefly, then discards it and reaches for a replacement. The grandmother grabs a fresh sock from a pack; the developer hits "regenerate" in their terminal. The parallel motion is synchronized — both acts of rational disposal happen in lockstep. This is the emotional callback that ties the entire video's thesis together: economics changed, so behavior changed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, full height, `rgba(255,255,255,0.10)`
- **Left Panel — Sock (X: 0-958)**
  - Label: "SOCKS" — `#94A3B8`, 14px, top-left at (80, 60), letter-spacing 3px
  - Holey sock silhouette: Simplified outline, `#D9944A` at 0.5 opacity, stroke 2px, centered at (480, 420). Three small holes rendered as gaps in the outline
  - Hand silhouette: Minimal geometric shape reaching from left edge toward sock, `rgba(255,255,255,0.15)`, stroke 1.5px
  - Discard motion: Sock fades and drifts downward (Y+40, opacity→0)
  - Fresh sock: Slides in from right side of panel, `#4A90D9` at 0.5 opacity, clean unbroken outline, centered at (480, 420)
  - Cost label: "$2" — `#5AAA6E`, 18px, appears below fresh sock at (480, 560)
- **Right Panel — Code (X: 962-1920)**
  - Label: "CODE" — `#94A3B8`, 14px, top-left at (1040, 60), letter-spacing 3px
  - Buggy code block: Simplified rectangle with wavy red underlines (3 squiggles), `rgba(255,255,255,0.12)` fill, `#EF4444` squiggles at 0.4 opacity, centered at (1440, 420)
  - Hand/cursor silhouette: Minimal geometric cursor approaching from left, `rgba(255,255,255,0.15)`
  - Discard motion: Code block fades and drifts downward (Y+40, opacity→0) — synchronized with sock
  - Terminal block: Slides in from right, dark rounded rect `#1E293B` with border `rgba(255,255,255,0.08)`, containing `pdd fix` in `#5AAA6E` JetBrains Mono, centered at (1440, 420)
  - Cost label: "~30s" — `#5AAA6E`, 18px, appears below terminal at (1440, 560)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider draws top-to-bottom. "SOCKS" and "CODE" labels fade in
2. **Frame 20-60 (0.67-2.0s):** Left: Holey sock fades in with hand approaching. Right: Buggy code block fades in with cursor approaching. Both scale 0.95→1.0
3. **Frame 60-90 (2.0-3.0s):** Pause — both figures "consider" the object. Subtle ambient pulse on the sock holes and code squiggles (opacity oscillates 0.3→0.5)
4. **Frame 90-140 (3.0-4.67s):** Synchronized discard — both objects drift down (Y+40) and fade out. Hand/cursor follow briefly then retract
5. **Frame 140-190 (4.67-6.33s):** Left: Fresh sock slides in from right (easeOut). Right: Terminal block slides in from right (easeOut). Cost labels fade in beneath each
6. **Frame 190-240 (6.33-8.0s):** Hold at final state. Fresh sock and terminal breathe with gentle 0.02 opacity oscillation. Cost labels hold steady

### Typography
- Panel Labels: Inter, 14px, medium (500), `#94A3B8`, letter-spacing 3px
- Cost Labels: Inter, 18px, semi-bold (600), `#5AAA6E`
- Terminal Text: JetBrains Mono, 14px, regular (400), `#5AAA6E`

### Easing
- Divider draw: `easeOut(cubic)`
- Object fade-in/scale: `easeOut(quad)`
- Discard drift: `easeIn(quad)` (gravity feel)
- Replacement slide-in: `easeOut(cubic)`
- Cost label fade: `easeOut(quad)`
- Ambient pulse: `easeInOut(sine)`

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Divider */}
  <Sequence from={0} durationInFrames={20}>
    <VerticalDivider x={960} color="rgba(255,255,255,0.10)" />
    <PanelLabel text="SOCKS" x={80} y={60} />
    <PanelLabel text="CODE" x={1040} y={60} />
  </Sequence>

  {/* Left Panel — Sock */}
  <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
    <Sequence from={20} durationInFrames={40}>
      <HoleySockSilhouette x={480} y={420} color="#D9944A" />
    </Sequence>
    <Sequence from={90} durationInFrames={50}>
      <DiscardMotion targetY={460} />
    </Sequence>
    <Sequence from={140} durationInFrames={50}>
      <FreshSockSlideIn x={480} y={420} color="#4A90D9" />
      <CostLabel text="$2" x={480} y={560} color="#5AAA6E" />
    </Sequence>
  </AbsoluteFill>

  {/* Right Panel — Code */}
  <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
    <Sequence from={20} durationInFrames={40}>
      <BuggyCodeBlock x={1440} y={420} squiggles={3} />
    </Sequence>
    <Sequence from={90} durationInFrames={50}>
      <DiscardMotion targetY={460} />
    </Sequence>
    <Sequence from={140} durationInFrames={50}>
      <TerminalBlock x={1440} y={420} command="pdd fix" color="#5AAA6E" />
      <CostLabel text="~30s" x={1440} y={560} color="#5AAA6E" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "divider": {
    "x": 960,
    "color": "rgba(255,255,255,0.10)",
    "width": 2
  },
  "leftPanel": {
    "label": "SOCKS",
    "oldItem": {
      "type": "holey_sock",
      "color": "#D9944A",
      "opacity": 0.5,
      "holes": 3
    },
    "newItem": {
      "type": "fresh_sock",
      "color": "#4A90D9",
      "opacity": 0.5
    },
    "cost": "$2"
  },
  "rightPanel": {
    "label": "CODE",
    "oldItem": {
      "type": "buggy_code",
      "squiggles": 3,
      "errorColor": "#EF4444"
    },
    "newItem": {
      "type": "terminal",
      "command": "pdd fix",
      "color": "#5AAA6E"
    },
    "cost": "~30s"
  }
}
```

---
