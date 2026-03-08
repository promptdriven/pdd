[split:]

# Section 1.6: Split-Screen Before/After Comparison

**Tool:** Remotion
**Duration:** ~2s (60 frames)
**Timestamp:** 0:07 - 0:09

## Visual Description
A split-screen layout divides the frame vertically into two halves. The left panel is labeled "Before" with a static image placeholder on a muted gray background, representing traditional video editing. The right panel is labeled "After" with an animated gradient background and floating code snippets, representing Remotion-powered automation. A vertical divider line wipes from top to bottom between the two panels. Each side has a small icon badge — a film-reel icon on the left and a code-bracket icon on the right.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (slate-950)
- Vertical divider at X=960

### Chart/Visual Elements
- **Left panel (Before):**
  - Background: #1E293B (slate-800)
  - Label "Before" at (240, 120), 48px Inter bold, #94A3B8
  - Film-reel icon: 40x40px SVG at (240, 200), #64748B
  - Static placeholder bars: 3 horizontal gray bars (#334155) at Y=350, Y=450, Y=550, widths 300px, 220px, 260px
- **Right panel (After):**
  - Background: Animated gradient 135deg from #1E3A8A to #0F172A, slowly shifting hue
  - Label "After" at (1200, 120), 48px Inter bold, #60A5FA
  - Code-bracket icon: 40x40px SVG at (1200, 200), #3B82F6
  - Floating code tokens: 5 small pill shapes with text like `<Sequence>`, `spring()`, `interpolate()`, drifting upward at varied speeds, #3B82F6 at 40% opacity
- **Divider line:** 4px wide, #3B82F6, full height, glow 20px blur at 30% opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Left panel slides in from left edge (X offset -960 to 0)
2. **Frame 8-20 (0.27-0.67s):** Divider line wipes top-to-bottom (height 0 to 1080px)
3. **Frame 12-25 (0.4-0.83s):** Right panel slides in from right edge (X offset +960 to 0)
4. **Frame 20-35 (0.67-1.17s):** "Before" label fades in, static bars appear sequentially
5. **Frame 25-40 (0.83-1.33s):** "After" label fades in, code tokens begin floating upward
6. **Frame 40-60 (1.33-2.0s):** Hold — left side static, right side code tokens continue drifting

### Typography
- Panel labels: Inter, 48px, bold (weight 700), #94A3B8 (left) / #60A5FA (right)
- Code tokens: JetBrains Mono, 16px, normal, #3B82F6

### Easing
- Panel slide-in: `easeOutCubic`
- Divider wipe: `easeInOutQuad`
- Label fade: `easeOutQuad`
- Token drift: `linear` (continuous)

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

Appears during the tail of Segment 2 (7.0s-9.0s). The split comparison visually contrasts traditional video (static) with Remotion (animated code), reinforcing the "only Remotion" message.

## Code Structure (Remotion)
```typescript
<Sequence from={210} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    <Sequence from={0}>
      <SlidingPanel side="left" background="#1E293B">
        <PanelLabel text="Before" color="#94A3B8" icon="film-reel" />
        <StaticBars count={3} color="#334155" />
      </SlidingPanel>
    </Sequence>
    <Sequence from={8}>
      <DividerLine color="#3B82F6" glowBlur={20} />
    </Sequence>
    <Sequence from={12}>
      <SlidingPanel side="right" background="gradient">
        <PanelLabel text="After" color="#60A5FA" icon="code-brackets" />
        <FloatingCodeTokens tokens={['<Sequence>', 'spring()', 'interpolate()']} />
      </SlidingPanel>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "panels": {
    "left": { "label": "Before", "background": "#1E293B", "accent": "#94A3B8" },
    "right": { "label": "After", "background": "gradient", "accent": "#60A5FA" }
  },
  "codeTokens": ["<Sequence>", "spring()", "interpolate()", "useCurrentFrame()", "<AbsoluteFill>"],
  "divider": { "color": "#3B82F6", "width": 4, "glowBlur": 20 }
}
```

---
