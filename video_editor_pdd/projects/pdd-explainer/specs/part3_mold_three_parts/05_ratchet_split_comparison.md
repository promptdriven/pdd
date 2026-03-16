[split:]

# Section 3.4: Ratchet Split — Code Bug vs. Prompt Defect

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 14:02 – 14:16

## Visual Description
A split-screen comparison distinguishing two types of defects in PDD: a code bug (left) and a prompt defect (right). Left panel shows a bug in the generated code — the fix is to add a new test wall, then regenerate. Right panel shows code that correctly implements a wrong specification — the fix is to edit the prompt (the mold itself), then regenerate. Both sides show the same regeneration step at the end, but the intervention point is different. This subtle but critical distinction is central to PDD's mental model.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Vertical divider: 2px, `rgba(255,255,255,0.12)`, centered at x=960

### Chart/Visual Elements
- **Left Panel — Code Bug (x: 0–958)**
  - Header: "Code Bug" — `#EF4444`, 22px, top-center at (480, 80)
  - Subheader: "Generated code violates intent" — `#94A3B8`, 14px
  - Step 1 visual: Mold with walls + code. Red spark (bug) in code area
  - Step 2 visual: New amber wall brick slides in → labeled "Add a wall"
  - Step 3 visual: Code regenerates (particles refill, clean)
  - Arrow flow: Step 1 → Step 2 → Step 3, vertical, connected by thin arrows
  - Intervention label: "Fix: Add a test" — `#D9944A`, 16px, bold

- **Right Panel — Prompt Defect (x: 962–1920)**
  - Header: "Prompt Defect" — `#4A90D9`, 22px, top-center at (1440, 80)
  - Subheader: "Code correctly implements wrong spec" — `#94A3B8`, 14px
  - Step 1 visual: Mold with walls + code. Code is green (passes tests!) but the cavity shape is wrong
  - Step 2 visual: The mold cavity shape morphs — labeled "Change the mold"
  - Step 3 visual: Code regenerates with new shape
  - Arrow flow: Step 1 → Step 2 → Step 3, vertical, connected by thin arrows
  - Intervention label: "Fix: Edit the prompt" — `#4A90D9`, 16px, bold

- **Bottom banner:** "PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the mold itself."
  - Centered at y=920, `#FFFFFF` at 0.6 opacity, 16px

### Animation Sequence
1. **Frame 0–20 (0–0.67s):** Vertical divider draws top-to-bottom. Headers "Code Bug" and "Prompt Defect" fade in simultaneously.
2. **Frame 20–60 (0.67–2.0s):** Subheaders fade in. Both Step 1 visuals appear — left shows bug spark in code, right shows green-passing code but with a misshapen cavity outline (dashed `#4A90D9` showing "wrong shape").
3. **Frame 60–150 (2.0–5.0s):** Left: Step 2 — new wall brick slides into the mold stack with amber flash. Arrow draws from Step 1 to Step 2. "Add a wall" label fades in. Right: Step 2 — the mold cavity outline morphs smoothly from wrong shape to correct shape. Arrow draws. "Change the mold" label fades in.
4. **Frame 150–240 (5.0–8.0s):** Both sides simultaneously: Step 3 — code particles dissolve and regenerate. Left: clean particles, no bug. Right: particles now conform to the corrected cavity shape. Arrows draw to Step 3.
5. **Frame 240–300 (8.0–10.0s):** Intervention labels fade in on each side — "Fix: Add a test" (amber) on left, "Fix: Edit the prompt" (blue) on right. Each gets a subtle left-border accent bar (4px).
6. **Frame 300–360 (10.0–12.0s):** Bottom banner types on character by character.
7. **Frame 360–420 (12.0–14.0s):** Hold. Both panels breathe with subtle ambient pulse. Divider pulses faintly.

### Typography
- Panel headers: Inter Bold, 22px, respective colors
- Subheaders: Inter Regular, 14px, `#94A3B8`
- Step labels: Inter Medium, 14px, `#FFFFFF` at 0.7 opacity
- Intervention labels: Inter SemiBold, 16px, respective colors, with 4px left accent bar
- Bottom banner: Inter Regular, 16px, `#FFFFFF` at 0.6 opacity

### Easing
- Divider draw: `easeOutCubic`
- Header fade: `easeOutQuad`
- Wall brick slide: `spring({ damping: 12, stiffness: 110 })`
- Cavity morph: `easeInOutCubic` (1s duration)
- Particle regeneration: `easeInOutCubic`
- Arrow draw: `easeOutQuad`
- Banner type-on: linear

## Narration Sync
> "And sometimes the bug isn't in the code — it's in the prompt. The code correctly implements a wrong specification. PDD distinguishes between these. A code bug? Add a wall. A prompt defect? Change the mold itself."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Divider */}
    <Sequence from={0} durationInFrames={20}>
      <VerticalDivider x={960} color="rgba(255,255,255,0.12)" />
    </Sequence>

    {/* Left Panel — Code Bug */}
    <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
      <Sequence from={0} durationInFrames={20}>
        <PanelHeader text="Code Bug" color="#EF4444" x={480} />
        <Subheader text="Generated code violates intent" x={480} />
      </Sequence>
      <Sequence from={20} durationInFrames={40}>
        <BugInCode x={480} y={320} />
      </Sequence>
      <Sequence from={60} durationInFrames={90}>
        <AddWallStep x={480} y={480} />
      </Sequence>
      <Sequence from={150} durationInFrames={90}>
        <RegenerateStep x={480} y={640} clean={true} />
      </Sequence>
      <Sequence from={240} durationInFrames={60}>
        <InterventionLabel text="Fix: Add a test" color="#D9944A" />
      </Sequence>
    </AbsoluteFill>

    {/* Right Panel — Prompt Defect */}
    <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
      <Sequence from={0} durationInFrames={20}>
        <PanelHeader text="Prompt Defect" color="#4A90D9" x={1440} />
        <Subheader text="Code correctly implements wrong spec" x={1440} />
      </Sequence>
      <Sequence from={20} durationInFrames={40}>
        <WrongShapeCode x={1440} y={320} />
      </Sequence>
      <Sequence from={60} durationInFrames={90}>
        <MoldMorphStep x={1440} y={480} />
      </Sequence>
      <Sequence from={150} durationInFrames={90}>
        <RegenerateStep x={1440} y={640} newShape={true} />
      </Sequence>
      <Sequence from={240} durationInFrames={60}>
        <InterventionLabel text="Fix: Edit the prompt" color="#4A90D9" />
      </Sequence>
    </AbsoluteFill>

    {/* Bottom banner */}
    <Sequence from={300} durationInFrames={60}>
      <TypeOnText
        text="A code bug? Add a wall. A prompt defect? Change the mold itself."
        y={920}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "leftPanel": {
    "title": "Code Bug",
    "subtitle": "Generated code violates intent",
    "color": "#EF4444",
    "intervention": "Add a test",
    "interventionColor": "#D9944A",
    "steps": ["Bug in code", "Add wall", "Regenerate (clean)"]
  },
  "rightPanel": {
    "title": "Prompt Defect",
    "subtitle": "Code correctly implements wrong spec",
    "color": "#4A90D9",
    "intervention": "Edit the prompt",
    "interventionColor": "#4A90D9",
    "steps": ["Wrong spec", "Morph mold", "Regenerate (new shape)"]
  }
}
```

---
