[title:]

# Section 7.7: Final Title Card — Prompt-Driven Development

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 25:08 - 25:20

## Visual Description
Fade to black from the previous scene. After a brief pause, the title "Prompt-Driven Development" fades in at the center of the screen — the same typography as the cold open's title card (Section 0.7) but without the ring-collapse animation. Clean, direct, final. Below the title, a thin accent line draws out. Below that, two monospace install/usage commands appear as an actionable call-to-action:

```
uv tool install pdd-cli
pdd update your_module.py
```

These are rendered in a subtle terminal-style block — not flashy, just practical. The message is: here's how to start. The URL "pdd.dev" appears below the commands as a simple, understated link.

The card holds for several seconds, giving the viewer time to note the commands and URL. Ambient particles from the 3Blue1Brown visual vocabulary drift upward. The mold wireframe glow from the previous scene is completely gone — this is a clean slate.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Radial gradient from center `#0F172A` to edges `#020617` (matching cold open title card)
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "Prompt-Driven Development" — white `#FFFFFF`, centered at (960, 360)
- **Upper Accent Line:** Horizontal rule, `#4A90D9` at 50% opacity, centered at Y=410, 400px wide x 1.5px tall
- **Command Block (centered at 960, 520):**
  - Background: `#0D1117` rounded rectangle, 520x100px, 8px border-radius, 1px border `#1E293B`
  - Line 1: `$ uv tool install pdd-cli` — `$` in `#4A5568`, command in `#E2E8F0`
  - Line 2: `$ pdd update your_module.py` — `$` in `#4A5568`, `pdd` in `#4A90D9`, rest in `#E2E8F0`
  - Line spacing: 28px between lines
  - Internal padding: 20px horizontal, 16px vertical

- **URL Text:** "pdd.dev" — `#4A90D9` at 70% opacity, centered at (960, 640)
- **Lower Accent Line:** Horizontal rule, `#4A90D9` at 30% opacity, centered at Y=600, 200px wide x 1px tall

- **Ambient Particles:** 10-12 small dots (2-3px), `#4A90D9` at 10-15% opacity, drifting upward slowly. Same style as cold open title card.

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Pure black. Breathing room after the previous scene's emotional beat.
2. **Frame 30-60 (1.0-2.0s):** Title text fades in (opacity 0→1) centered. Clean, weighted appearance.
3. **Frame 60-80 (2.0-2.67s):** Upper accent line draws from center outward (width 0→400px). Symmetric expansion.
4. **Frame 80-130 (2.67-4.33s):** Command block fades in (opacity 0→1, translateY 8→0):
   - **Frame 80-100:** Block background appears
   - **Frame 100-115:** First command line types in (typewriter effect, ~3 chars/frame)
   - **Frame 115-130:** Second command line types in
5. **Frame 130-150 (4.33-5.0s):** Lower accent line draws from center outward (width 0→200px).
6. **Frame 150-170 (5.0-5.67s):** URL "pdd.dev" fades in below lower accent line.
7. **Frame 170-200 (5.67-6.67s):** Ambient particles begin drifting upward.
8. **Frame 200-360 (6.67-12.0s):** Hold. All elements at final state. Particles continue drifting. The card is fully established, giving the viewer time to absorb the commands and URL.

### Typography
- Title: Inter, 56px, bold (700), `#FFFFFF`, letter-spacing: 2px
- Command prompt (`$`): JetBrains Mono, 16px, regular, `#4A5568`
- Command text: JetBrains Mono, 16px, regular, `#E2E8F0`
- `pdd` keyword: JetBrains Mono, 16px, regular, `#4A90D9`
- URL: Inter, 20px, regular (400), `#4A90D9` at 70% opacity, letter-spacing: 1px
- Accent lines: no text

### Easing
- Title fade-in: `easeOut(quad)`
- Accent line draw: `easeOut(cubic)`
- Command block fade + drift: `easeOut(quad)`
- Typewriter: `linear` (fixed chars/frame)
- URL fade-in: `easeOut(quad)`
- Particle drift: `linear`

## Narration Sync
> (No narration — title card with ambient music / tone. The visual is the call to action.)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <RadialGradientBg center="#0F172A" edge="#020617" />

  {/* Title */}
  <Sequence from={30}>
    <FadeIn durationInFrames={30}>
      <CenteredText
        text="Prompt-Driven Development"
        position={[960, 360]}
        font="Inter"
        size={56}
        weight={700}
        color="#FFFFFF"
        letterSpacing={2}
      />
    </FadeIn>
  </Sequence>

  {/* Upper Accent Line */}
  <Sequence from={60}>
    <ExpandingLine
      y={410}
      targetWidth={400}
      color="#4A90D9"
      opacity={0.5}
      thickness={1.5}
      durationInFrames={20}
    />
  </Sequence>

  {/* Command Block */}
  <Sequence from={80}>
    <FadeInDrift drift={-8} durationInFrames={20}>
      <CommandBlock
        position={[960, 520]}
        width={520}
        height={100}
        background="#0D1117"
        borderColor="#1E293B"
        borderRadius={8}
        padding={[20, 16]}
      >
        <Sequence from={20}>
          <TypewriterLine
            text="$ uv tool install pdd-cli"
            charsPerFrame={3}
            colors={{ "$": "#4A5568", default: "#E2E8F0" }}
          />
        </Sequence>
        <Sequence from={35}>
          <TypewriterLine
            text="$ pdd update your_module.py"
            charsPerFrame={3}
            colors={{ "$": "#4A5568", "pdd": "#4A90D9", default: "#E2E8F0" }}
          />
        </Sequence>
      </CommandBlock>
    </FadeInDrift>
  </Sequence>

  {/* Lower Accent Line */}
  <Sequence from={130}>
    <ExpandingLine
      y={600}
      targetWidth={200}
      color="#4A90D9"
      opacity={0.3}
      thickness={1}
      durationInFrames={20}
    />
  </Sequence>

  {/* URL */}
  <Sequence from={150}>
    <FadeIn durationInFrames={20}>
      <CenteredText
        text="pdd.dev"
        position={[960, 640]}
        font="Inter"
        size={20}
        color="#4A90D9"
        opacity={0.7}
        letterSpacing={1}
      />
    </FadeIn>
  </Sequence>

  {/* Ambient Particles */}
  <Sequence from={170}>
    <AmbientParticles
      count={11}
      color="#4A90D9"
      opacityRange={[0.1, 0.15]}
      sizeRange={[2, 3]}
      driftDirection="up"
      speed={0.25}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": {
    "text": "Prompt-Driven Development",
    "position": [960, 360],
    "color": "#FFFFFF",
    "fontSize": 56,
    "fontWeight": 700,
    "letterSpacing": 2
  },
  "upperAccentLine": {
    "y": 410,
    "width": 400,
    "color": "#4A90D9",
    "opacity": 0.5,
    "thickness": 1.5
  },
  "commandBlock": {
    "position": [960, 520],
    "width": 520,
    "height": 100,
    "background": "#0D1117",
    "borderColor": "#1E293B",
    "borderRadius": 8,
    "commands": [
      { "text": "uv tool install pdd-cli", "prefix": "$" },
      { "text": "pdd update your_module.py", "prefix": "$", "highlight": { "pdd": "#4A90D9" } }
    ],
    "textColor": "#E2E8F0",
    "prefixColor": "#4A5568"
  },
  "lowerAccentLine": {
    "y": 600,
    "width": 200,
    "color": "#4A90D9",
    "opacity": 0.3,
    "thickness": 1
  },
  "url": {
    "text": "pdd.dev",
    "position": [960, 640],
    "color": "#4A90D9",
    "opacity": 0.7,
    "fontSize": 20
  },
  "particles": {
    "count": 11,
    "color": "#4A90D9",
    "opacityRange": [0.1, 0.15],
    "sizeRange": [2, 3]
  },
  "background": {
    "center": "#0F172A",
    "edge": "#020617"
  }
}
```

---
