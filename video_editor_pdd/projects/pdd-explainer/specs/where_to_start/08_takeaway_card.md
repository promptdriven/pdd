[title:]

# Section 6.8: Takeaway Card — One Module, This Week

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:46 - 23:54

## Visual Description
A closing card for the section — a single, memorable call-to-action. The screen distills the entire "Where to Start" section into one line: "Pick one module. This week." The typography is large, confident, and centered. Below it, three small icons recap the key steps in miniature: a leaf node icon (pick a leaf), a terminal prompt icon (three commands), and a gauge icon (watch the ratchet). The card functions as both the section's emotional punctuation mark and a practical takeaway the viewer can act on immediately. It's the frame they'd screenshot and share.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` with subtle radial gradient — center brightens to `#131E30` at 40% radius, fading back to `#0F172A` at edges. Creates a subtle "spotlight" feel
- Grid lines: None

### Chart/Visual Elements
- **Main Text (centered, Y=400):**
  - Line 1: "Pick one module." — `#FFFFFF`, 48px bold
  - Line 2: "This week." — `#4A90D9`, 48px bold, appearing below Line 1 with 20px gap
  - Both lines center-aligned at X=960
- **Thin Accent Bar:** Horizontal, 60px wide x 2px, `rgba(255,255,255,0.3)`, centered at Y=510
- **Recap Icons (Y=580, horizontally centered, 200px spacing):**
  - Icon 1 (X=760): Leaf node — simplified tree branch ending in a circle, `#4A90D9` at 0.4, 32px
    - Label below: "Find a leaf" — Inter 12px, `#94A3B8`
  - Icon 2 (X=960): Terminal prompt — `>_` cursor symbol, `#5AAA6E` at 0.4, 32px
    - Label below: "Three commands" — Inter 12px, `#94A3B8`
  - Icon 3 (X=1160): Gauge — simplified circular arc with arrow, `#D9944A` at 0.4, 32px
    - Label below: "Watch it grow" — Inter 12px, `#94A3B8`
- **Connecting dots:** Three small dots (4px each, `rgba(255,255,255,0.1)`) between the icons, at Y=590

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Background radial gradient subtly intensifies (spotlight brightens)
2. **Frame 10-50 (0.33-1.67s):** "Pick one module." fades in with slight scale (0.9→1.0). Clean, centered
3. **Frame 50-90 (1.67-3.0s):** "This week." fades in below — blue color adds urgency. Slight upward drift (8px)
4. **Frame 90-120 (3.0-4.0s):** Accent bar draws from center outward (0→60px)
5. **Frame 120-200 (4.0-6.67s):** Recap icons appear with 20-frame stagger:
   - Icon 1 (leaf) fades in with slight scale. Label appears below
   - Connecting dots fade in
   - Icon 2 (terminal) fades in. Label appears
   - Connecting dots fade in
   - Icon 3 (gauge) fades in. Label appears
6. **Frame 200-240 (6.67-8.0s):** Hold at final state. "This week." text has very subtle pulse (opacity 0.95→1.0, repeating). Icons steady

### Typography
- Main Text Line 1: Inter, 48px, bold (700), `#FFFFFF`
- Main Text Line 2: Inter, 48px, bold (700), `#4A90D9`
- Icon Labels: Inter, 12px, regular (400), `#94A3B8`

### Easing
- Background spotlight: `easeInOut(sine)`
- "Pick one module." fade/scale: `easeOut(quad)`
- "This week." fade/drift: `easeOut(quad)`
- Accent bar draw: `easeOut(cubic)`
- Icon appear: `easeOut(back(1.2))`
- Icon labels: `easeOut(quad)`
- Text pulse: `easeInOut(sine)`

## Narration Sync
> "Pick one module. This week. Find a leaf, run three commands, and watch the ratchet start to turn. That's all it takes to begin."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Background Spotlight */}
  <Sequence from={0} durationInFrames={20}>
    <RadialGradientShift center="#131E30" edge="#0F172A" />
  </Sequence>

  {/* Main Text */}
  <Sequence from={10} durationInFrames={40}>
    <FadeScaleText text="Pick one module." fontSize={48} color="#FFFFFF" y={400} />
  </Sequence>
  <Sequence from={50} durationInFrames={40}>
    <FadeDriftText text="This week." fontSize={48} color="#4A90D9" y={468} drift={8} />
  </Sequence>

  {/* Accent Bar */}
  <Sequence from={90} durationInFrames={30}>
    <AccentLine targetWidth={60} y={510} color="rgba(255,255,255,0.3)" />
  </Sequence>

  {/* Recap Icons */}
  {recapIcons.map((icon, i) => (
    <Sequence key={icon.id} from={120 + i * 20} durationInFrames={30}>
      <RecapIcon
        type={icon.type}
        color={icon.color}
        label={icon.label}
        x={icon.x}
        y={580}
      />
    </Sequence>
  ))}
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "backgroundSpotlight": "#131E30",
  "mainText": {
    "line1": { "text": "Pick one module.", "color": "#FFFFFF", "fontSize": 48 },
    "line2": { "text": "This week.", "color": "#4A90D9", "fontSize": 48 }
  },
  "accentBar": {
    "width": 60,
    "y": 510,
    "color": "rgba(255,255,255,0.3)"
  },
  "recapIcons": [
    { "type": "leaf", "label": "Find a leaf", "color": "#4A90D9", "x": 760 },
    { "type": "terminal", "label": "Three commands", "color": "#5AAA6E", "x": 960 },
    { "type": "gauge", "label": "Watch it grow", "color": "#D9944A", "x": 1160 }
  ]
}
```

---
