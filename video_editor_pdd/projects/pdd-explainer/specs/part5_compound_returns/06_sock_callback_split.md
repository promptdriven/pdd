[split:]

# Section 5.6: Sock Callback — Grandmother and Developer Return

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 21:52 - 22:02

## Visual Description
The sock metaphor returns for its emotional payoff. A split-screen brings back both characters from the cold open: the 1950s grandmother on the left and the modern developer on the right. This time the framing is different — instead of showing them working, it shows the *realization*. The grandmother puts down her darning needle; the developer puts down their patching tools. Both recognize the economics have changed. The visual callbacks to the opening create narrative closure while driving the argument home: rational behavior changes when economics change.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, full height, `rgba(255,255,255,0.12)`
- **Left Panel — Grandmother (X: 0-958)**
  - Label: "1960s" — `#94A3B8`, 20px, top-left at (80, 60)
  - Stylized grandmother silhouette: Seated figure, simplified geometric shapes, stroke `#D9944A` at 0.4 opacity, 2px, centered at (480, 480)
  - Darning needle: Small diagonal line, `#D9944A` at 0.6 opacity, starting in hand position
  - Sock: Small rounded rectangle near hands, `#D9944A` at 0.3 opacity
  - Decision: Needle drops away (rotates and fades), sock placed aside
  - New sock pack: Appears to the right of figure, `#4A90D9` at 0.4 opacity, labeled "×12" in small text
  - Caption: "Your great-grandmother wasn't stupid for darning socks." — `#FFFFFF` at 0.6 opacity, 16px, positioned at (480, 850), max-width 380px, centered
- **Right Panel — Developer (X: 962-1920)**
  - Label: "2025" — `#94A3B8`, 20px, top-left at (1040, 60)
  - Stylized developer silhouette: Seated at desk, simplified geometric shapes, stroke `#4A90D9` at 0.4 opacity, 2px, centered at (1440, 480)
  - Code editor: Rectangular outline behind developer, `rgba(255,255,255,0.08)`, representing Cursor/IDE
  - Patch icon: Small wrench/bandage icon near the editor, `#D9944A` at 0.6 opacity
  - Decision: Patch icon drops away (rotates and fades), editor screen shifts to show a prompt file
  - Terminal snippet: Small text block at bottom-right of editor: `pdd generate` — JetBrains Mono, `#5AAA6E` at 0.4 opacity, 12px
  - Caption: "And you're not stupid for patching code." — `#FFFFFF` at 0.6 opacity, 16px, positioned at (1440, 850), max-width 380px, centered

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider draws top-to-bottom. Era labels "1960s" and "2025" fade in
2. **Frame 20-60 (0.67-2.0s):** Both silhouettes fade in simultaneously with slight scale-up (0.95→1.0). Grandmother holds needle over sock; developer has cursor in code editor with patch icon
3. **Frame 60-120 (2.0-4.0s):** Left: Grandmother pauses. The needle begins to rotate slowly (suggesting putting it down). Right: Developer pauses. The patch icon begins to rotate similarly
4. **Frame 120-180 (4.0-6.0s):** Left: Needle drops away (falls with gravity, rotates 45°, fades to 0). Sock placed aside. New sock pack slides in from right edge. Right: Patch icon drops away (same motion). Editor morphs — raw code fades, replaced by a clean prompt file outline. Terminal snippet appears
5. **Frame 180-240 (6.0-8.0s):** Left caption fades in: "Your great-grandmother wasn't stupid for darning socks." Right caption fades in (20-frame stagger): "And you're not stupid for patching code."
6. **Frame 240-300 (8.0-10.0s):** Hold. Both panels breathe — very subtle ambient pulse on the new items (sock pack, prompt file) at 0.02 opacity oscillation

### Typography
- Era Labels: Inter, 20px, medium (500), `#94A3B8`
- Captions: Inter, 16px, regular (400), `#FFFFFF` at 0.6 opacity, max-width 380px, text-align center
- Terminal Text: JetBrains Mono, 12px, regular (400), `#5AAA6E` at 0.4 opacity

### Easing
- Divider draw: `easeOut(cubic)`
- Silhouette fade/scale: `easeOut(quad)`
- Needle/patch drop: `easeIn(quad)` (gravity feel)
- New item slide-in: `easeOut(cubic)`
- Editor morph: `easeInOut(cubic)`
- Caption fade: `easeOut(quad)`

## Narration Sync
> "Your great-grandmother wasn't stupid for darning socks. The economics made it rational."
> "And you're not stupid for patching code. Until now, the economics made it rational."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Divider */}
  <Sequence from={0} durationInFrames={20}>
    <VerticalDivider x={960} color="rgba(255,255,255,0.12)" />
    <EraLabel text="1960s" x={80} y={60} />
    <EraLabel text="2025" x={1040} y={60} />
  </Sequence>

  {/* Left Panel — Grandmother */}
  <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
    <Sequence from={20} durationInFrames={40}>
      <GrandmotherSilhouette x={480} y={480} color="#D9944A" />
    </Sequence>
    <Sequence from={60} durationInFrames={120}>
      <NeedleDrop startFrame={60} endFrame={120} />
      <Sequence from={60}>
        <SockPackSlideIn x={620} color="#4A90D9" label="×12" />
      </Sequence>
    </Sequence>
    <Sequence from={180}>
      <Caption
        text="Your great-grandmother wasn't stupid for darning socks."
        x={480}
        y={850}
        maxWidth={380}
      />
    </Sequence>
  </AbsoluteFill>

  {/* Right Panel — Developer */}
  <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
    <Sequence from={20} durationInFrames={40}>
      <DeveloperSilhouette x={1440} y={480} color="#4A90D9" />
      <CodeEditor x={1440} y={400} />
    </Sequence>
    <Sequence from={60} durationInFrames={120}>
      <PatchIconDrop startFrame={60} endFrame={120} />
      <Sequence from={60}>
        <EditorMorph from="code" to="prompt" />
        <TerminalSnippet text="pdd generate" color="#5AAA6E" />
      </Sequence>
    </Sequence>
    <Sequence from={200}>
      <Caption
        text="And you're not stupid for patching code."
        x={1440}
        y={850}
        maxWidth={380}
      />
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
    "color": "rgba(255,255,255,0.12)",
    "width": 2
  },
  "leftPanel": {
    "era": "1960s",
    "silhouette": { "x": 480, "y": 480, "color": "#D9944A", "opacity": 0.4 },
    "needle": { "color": "#D9944A", "dropRotation": 45 },
    "sockPack": { "color": "#4A90D9", "opacity": 0.4, "label": "×12" },
    "caption": "Your great-grandmother wasn't stupid for darning socks."
  },
  "rightPanel": {
    "era": "2025",
    "silhouette": { "x": 1440, "y": 480, "color": "#4A90D9", "opacity": 0.4 },
    "patchIcon": { "color": "#D9944A", "dropRotation": 45 },
    "terminal": { "text": "pdd generate", "color": "#5AAA6E" },
    "caption": "And you're not stupid for patching code."
  }
}
```

---
