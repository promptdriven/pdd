[split:Prompt vs Generated Code] Side-by-Side Specification and Implementation

# Section 3.5: Split Screen — Prompt Spec vs Generated Code

**Tool:** Remotion
**Duration:** ~12s
**Timestamp:** 2:20 - 2:32

## Visual Description
A split-screen comparison divides the frame vertically. The left half is labeled "PROMPT" and shows a compact natural-language specification (~8-10 lines of intent-focused text in a code editor aesthetic). The right half is labeled "GENERATED CODE" and shows a much longer block of implementation code (~40+ lines, scrolling). The key visual contrast: the prompt is 1/5 to 1/10 the size of the code. A line counter appears on each side showing the ratio. The left side has a warm gold tint; the right side has a cool blue tint. The code on the right auto-scrolls slowly to emphasize length, while the prompt on the left stays static — reinforcing that the prompt captures intent concisely.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Left panel: (40, 80) to (930, 1000), semi-transparent dark backing
- Right panel: (990, 80) to (1880, 1000), semi-transparent dark backing
- Divider: vertical line at x=960, 2px, glowing

### Chart/Visual Elements
- Left panel ("Prompt"):
  - Background: rgba(245, 158, 11, 0.06) — faint gold tint
  - Header badge: "PROMPT" in gold (#F59E0B), small rounded pill
  - Code block: monospace text, ~8 lines, gold syntax highlighting
  - Line counter: "8 lines" in gold at bottom-left corner
  - Editor chrome: subtle line numbers, dark gutter
- Right panel ("Generated Code"):
  - Background: rgba(59, 130, 246, 0.06) — faint blue tint
  - Header badge: "GENERATED CODE" in blue (#3B82F6), small rounded pill
  - Code block: monospace text, ~50 lines, blue syntax highlighting, auto-scrolling
  - Line counter: "47 lines" in blue at bottom-left corner, animating up from 0
  - Editor chrome: subtle line numbers, dark gutter
- Divider: 2px vertical line, white at 30% opacity, soft glow
- Ratio callout: "~6x" appears centered between panels after both load, in white

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Left panel slides in from left — translateX(-400)→translateX(0), opacity 0→1.
2. **Frame 5-30 (0.17-1s):** Right panel slides in from right — translateX(400)→translateX(0), opacity 0→1.
3. **Frame 20-35 (0.67-1.17s):** Divider fades in — opacity 0→0.3, glow appears.
4. **Frame 25-50 (0.83-1.67s):** Prompt text types in line-by-line on left panel.
5. **Frame 30-60 (1-2s):** Code begins appearing on right panel, line counter animates 0→47.
6. **Frame 60-90 (2-3s):** Right panel code begins slow auto-scroll downward.
7. **Frame 80-100 (2.67-3.33s):** Ratio "~6x" fades in at center — scale 0.8→1.0, opacity 0→1.
8. **Frame 90-100 (3-3.33s):** Left line counter "8 lines" pulses gold.
9. **Frame 100-310 (3.33-10.33s):** Hold. Right panel continues slow scroll.
10. **Frame 310-360 (10.33-12s):** Both panels slide out — left to left, right to right. Divider fades.

### Typography
- Header badges: Inter SemiBold, 14px, uppercase, letter-spacing 0.1em
  - Left: #F59E0B on rgba(245, 158, 11, 0.15) pill
  - Right: #3B82F6 on rgba(59, 130, 246, 0.15) pill
- Code text: JetBrains Mono, 14px
  - Left: #FDE68A (light gold) for keywords, #F59E0B for strings
  - Right: #93C5FD (light blue) for keywords, #3B82F6 for strings
- Line counters: Inter Medium, 18px
  - Left: #F59E0B
  - Right: #3B82F6
- Ratio callout: Inter Black, 48px, #FFFFFF, text-shadow 0 4px 24px rgba(255,255,255,0.3)
- Source: none (self-evident comparison)

### Easing
- Panel slides: `spring({ damping: 16, stiffness: 160 })`
- Code typing: linear (character-by-character)
- Line counter: `easeOutCubic`
- Ratio scale: `easeOutQuart`
- Auto-scroll: `linear` (steady scroll)
- Panel slide out: `easeInCubic`

## Narration Sync
> "The prompt specifies what and why — not how. It's one-fifth to one-tenth the size of the code it replaces."

Left panel appears on "prompt specifies what and why." Right panel appears simultaneously. The ratio "~6x" callout emphasizes "one-fifth to one-tenth the size."

## Code Structure (Remotion)
```typescript
<Sequence from={SPLIT_START} durationInFrames={360}>
  <AbsoluteFill>
    {/* Left panel — Prompt */}
    <SplitPanel
      side="left"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 310, 360], [-400, 0, 0, -400])}px)`,
        opacity: interpolate(frame, [0, 25, 310, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelBadge text="PROMPT" color="#F59E0B" />
      <CodeBlock
        lines={promptLines}
        typeIn={{ startFrame: 25, charsPerFrame: 2 }}
        syntaxTheme="gold"
      />
      <LineCounter
        value={8}
        color="#F59E0B"
        opacity={interpolate(frame, [45, 60], [0, 1])}
      />
    </SplitPanel>

    {/* Divider */}
    <VerticalDivider
      opacity={interpolate(frame, [20, 35, 310, 360], [0, 0.3, 0.3, 0])}
      glowColor="#FFFFFF"
    />

    {/* Right panel — Generated Code */}
    <SplitPanel
      side="right"
      style={{
        transform: `translateX(${interpolate(frame, [5, 30, 310, 360], [400, 0, 0, 400])}px)`,
        opacity: interpolate(frame, [5, 30, 310, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelBadge text="GENERATED CODE" color="#3B82F6" />
      <ScrollingCodeBlock
        lines={generatedLines}
        scrollSpeed={0.5}
        startScrollFrame={60}
        syntaxTheme="blue"
      />
      <LineCounter
        value={Math.round(interpolate(frame, [30, 60], [0, 47], { extrapolateRight: 'clamp' }))}
        color="#3B82F6"
      />
    </SplitPanel>

    {/* Ratio callout */}
    <RatioCallout
      text="~6x"
      style={{
        opacity: interpolate(frame, [80, 100, 310, 360], [0, 1, 1, 0]),
        transform: `scale(${interpolate(frame, [80, 100], [0.8, 1.0], { extrapolateRight: 'clamp' })})`,
      }}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "prompt": {
    "label": "PROMPT",
    "line_count": 8,
    "color": "#F59E0B"
  },
  "generated": {
    "label": "GENERATED CODE",
    "line_count": 47,
    "color": "#3B82F6"
  },
  "ratio": "~6x",
  "totalFrames": 360,
  "fps": 30
}
```

---
