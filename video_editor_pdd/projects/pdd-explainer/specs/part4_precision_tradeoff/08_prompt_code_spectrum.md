[Remotion]

# Section 4.8: Prompt-Code Spectrum — Language to Code Slider

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 19:40 - 20:00

## Visual Description
A horizontal spectrum bar fills the lower-center of the screen. The LEFT end is labeled "Pure natural language" in blue, the RIGHT end "Pure code" in a neutral gray. A slider/marker sits on the spectrum, initially at the far left, then shifts to show where PDD operates — mostly to the left (natural language side), with a few notch marks further right for code-critical sections. Above the spectrum, a prompt document illustration shows natural-language text with an embedded code block — the code block has sharp monospace edges while the surrounding prose flows more organically. Labels explain: "Stay in prompt space as long as possible. Dip into code when you must." The visual makes clear that the boundary between prompt and code is fluid, not binary.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Spectrum Bar:** Centered horizontally, Y=700, 1400px wide x 16px tall, rounded corners 8px
  - Gradient fill: `#4A90D9` (left, pure NL) → `#64748B` (center, mixed) → `#94A3B8` (right, pure code)
  - Border: `rgba(255,255,255,0.1)`, 1px
- **Left Label:** "Pure natural language" — Inter 15px semi-bold, `#4A90D9`, positioned at left end of bar (260, 740)
- **Right Label:** "Pure code" — Inter 15px semi-bold, `#94A3B8`, positioned at right end of bar (1540, 740), right-aligned
- **Slider Marker:** Rounded rectangle 8px wide x 28px tall, `#FFFFFF`, positioned at ~25% from left (initial), with a soft glow `rgba(255,255,255,0.3)` 12px blur
- **PDD Zone Indicator:** Bracket/brace spanning from ~10% to ~35% of the bar, `#4A90D9` at 0.3 opacity, 2px stroke, with label "PDD operates here" below in `#4A90D9` at 0.5 opacity, 12px
- **Code Notch Marks:** 3 small ticks at ~60%, ~75%, ~90% of the bar, `#94A3B8` at 0.4 opacity, 2px wide x 10px tall, each with tiny labels: "algorithm", "inner loop", "bit ops" — JetBrains Mono 9px, `#94A3B8` at 0.3 opacity
- **Prompt Document (above spectrum):** Centered at (960, 360), 700px wide x 260px tall
  - Document background: `#1E293B`, border `rgba(255,255,255,0.06)` 1px, rounded corners 6px
  - Natural language lines: 14 horizontal "text lines", varying width (60-90% of document width), `#4A90D9` at 0.25 opacity, 3px tall, 8px spacing — organic, slightly irregular lengths
  - Embedded code block: A distinct 200px wide x 60px tall region at lines 8-11, background `#0F172A`, border `rgba(148,163,184,0.2)` 1px, containing 4 shorter "code lines" in `#94A3B8` at 0.35 opacity, uniform width, monospace feel (evenly spaced "characters" as tiny dots)
  - Label above document: "A prompt with embedded code" — Inter 14px, `#94A3B8` at 0.5 opacity
  - Arrow from code block pointing right toward the "code" end of spectrum, dashed, `rgba(148,163,184,0.2)`, 1px
  - Arrow from NL text pointing left toward "NL" end of spectrum, dashed, `rgba(74,144,217,0.2)`, 1px
- **Summary Label:** "The boundary between prompt and code is fluid." — Inter 20px medium, `#FFFFFF` at 0.6 opacity, centered at Y=820

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Spectrum bar draws in from center outward (expanding from 0 to full 1400px width). Left and right labels fade in
2. **Frame 40-80 (1.33-2.67s):** Prompt document fades in above spectrum. Natural language lines appear with left-to-right wipe, staggered. Label "A prompt with embedded code" fades in
3. **Frame 80-120 (2.67-4.0s):** Embedded code block within document highlights — border brightens from 0.2→0.5 opacity, background darkens slightly. Code lines appear. The visual distinction between NL and code regions is clear
4. **Frame 120-160 (4.0-5.33s):** Connecting arrows draw from document to spectrum — NL arrow to left, code arrow to right. Establishes the mapping between document regions and spectrum positions
5. **Frame 160-220 (5.33-7.33s):** Slider appears at far-left position (0%) and begins sliding right. It pauses at ~25% — the "sweet spot" for PDD. PDD zone bracket draws in around the slider position
6. **Frame 220-300 (7.33-10.0s):** Code notch marks fade in at 60%, 75%, 90% positions with tiny labels. These are the exceptions — the rare moments you need pure code
7. **Frame 300-360 (10.0-12.0s):** Slider makes brief, quick hops to the notch positions (60%, 75%) and back to 25%, showing that PDD "dips into code" occasionally but returns to prompt space. Each hop takes ~15 frames
8. **Frame 360-480 (12.0-16.0s):** "The boundary between prompt and code is fluid." label fades in at bottom. Summary label for the section
9. **Frame 480-540 (16.0-18.0s):** Subtitle appears: "Stay in prompt space as long as possible. Dip into code when you must." — Inter 16px, `#94A3B8` at 0.5 opacity, at Y=860
10. **Frame 540-600 (18.0-20.0s):** Hold at final state. Slider rests at ~25%. Subtle breathing pulse on the PDD zone bracket

### Typography
- Spectrum Left Label: Inter, 15px, semi-bold (600), `#4A90D9`
- Spectrum Right Label: Inter, 15px, semi-bold (600), `#94A3B8`
- PDD Zone Label: Inter, 12px, regular (400), `#4A90D9` at 0.5 opacity
- Notch Labels: JetBrains Mono, 9px, regular (400), `#94A3B8` at 0.3 opacity
- Document Label: Inter, 14px, regular (400), `#94A3B8` at 0.5 opacity
- Summary Label: Inter, 20px, medium (500), `#FFFFFF` at 0.6 opacity
- Subtitle: Inter, 16px, regular (400), `#94A3B8` at 0.5 opacity

### Easing
- Spectrum bar expand: `easeOut(cubic)`
- Document fade/wipe: `easeOut(quad)`
- Code block highlight: `easeInOut(sine)`
- Arrow draw: `easeOut(quad)`
- Slider initial slide: `easeInOut(cubic)`
- Slider hops: `easeInOut(back)` (slight overshoot on arrival)
- PDD zone bracket draw: `easeOut(quad)`
- Notch marks fade: `easeOut(quad)`
- Summary label fade: `easeOut(quad)`
- Breathing pulse: `easeInOut(sine)`

## Narration Sync
> "But some things genuinely need code-level precision. Algorithm choice. Performance-critical inner loops. Bit-level operations."
> "PDD handles this. A prompt can embed code snippets for exactly those critical sections. It's not all-or-nothing. You stay in prompt space for as long as possible — architecture, intent, constraints, edge cases — then dip into code when the precision demands it."
> "Think of it as a spectrum. Natural language on one end, code on the other. The question isn't 'prompts OR code.' It's 'how far into prompt space can you stay?' For most of the specification — further than you'd think."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Spectrum Bar */}
  <Sequence from={0} durationInFrames={40}>
    <SpectrumBar
      y={700}
      width={1400}
      height={16}
      gradient={["#4A90D9", "#64748B", "#94A3B8"]}
    />
    <SpectrumLabels
      left={{ text: "Pure natural language", color: "#4A90D9" }}
      right={{ text: "Pure code", color: "#94A3B8" }}
    />
  </Sequence>

  {/* Prompt Document */}
  <Sequence from={40} durationInFrames={80}>
    <PromptDocumentWithCode
      x={610} y={230} width={700} height={260}
      nlLineCount={14}
      codeBlock={{ x: 250, y: 96, width: 200, height: 60, lines: 4 }}
    />
    <Label text="A prompt with embedded code" x={960} y={210} centered />
  </Sequence>

  {/* Code Block Highlight */}
  <Sequence from={80} durationInFrames={40}>
    <CodeBlockHighlight targetOpacity={0.5} />
  </Sequence>

  {/* Connecting Arrows */}
  <Sequence from={120} durationInFrames={40}>
    <ConnectingArrow from="nlRegion" to="spectrumLeft" color="rgba(74,144,217,0.2)" />
    <ConnectingArrow from="codeRegion" to="spectrumRight" color="rgba(148,163,184,0.2)" />
  </Sequence>

  {/* Slider + PDD Zone */}
  <Sequence from={160} durationInFrames={60}>
    <SpectrumSlider
      initialPosition={0}
      targetPosition={0.25}
      markerWidth={8}
      markerHeight={28}
      color="#FFFFFF"
    />
    <PDDZoneBracket from={0.10} to={0.35} color="#4A90D9" label="PDD operates here" />
  </Sequence>

  {/* Code Notch Marks */}
  <Sequence from={220} durationInFrames={80}>
    <NotchMarks
      positions={[0.60, 0.75, 0.90]}
      labels={["algorithm", "inner loop", "bit ops"]}
      color="#94A3B8"
    />
  </Sequence>

  {/* Slider Hops */}
  <Sequence from={300} durationInFrames={60}>
    <SliderHops
      homePosition={0.25}
      hopTargets={[0.60, 0.75]}
      framesPerHop={15}
    />
  </Sequence>

  {/* Summary Labels */}
  <Sequence from={360} durationInFrames={120}>
    <FadeIn>
      <SummaryLabel
        text="The boundary between prompt and code is fluid."
        y={820}
        fontSize={20}
        color="#FFFFFF"
        opacity={0.6}
      />
    </FadeIn>
  </Sequence>

  <Sequence from={480} durationInFrames={60}>
    <FadeIn>
      <SubtitleLabel
        text="Stay in prompt space as long as possible. Dip into code when you must."
        y={860}
        fontSize={16}
        color="#94A3B8"
        opacity={0.5}
      />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "spectrum": {
    "y": 700,
    "width": 1400,
    "height": 16,
    "gradient": ["#4A90D9", "#64748B", "#94A3B8"],
    "leftLabel": "Pure natural language",
    "rightLabel": "Pure code"
  },
  "slider": {
    "width": 8,
    "height": 28,
    "color": "#FFFFFF",
    "homePosition": 0.25,
    "glowColor": "rgba(255,255,255,0.3)",
    "glowBlur": 12
  },
  "pddZone": {
    "start": 0.10,
    "end": 0.35,
    "color": "#4A90D9",
    "opacity": 0.3,
    "label": "PDD operates here"
  },
  "codeNotches": [
    { "position": 0.60, "label": "algorithm" },
    { "position": 0.75, "label": "inner loop" },
    { "position": 0.90, "label": "bit ops" }
  ],
  "promptDocument": {
    "width": 700,
    "height": 260,
    "nlLines": 14,
    "codeBlock": {
      "width": 200,
      "height": 60,
      "lines": 4
    }
  },
  "summaryText": "The boundary between prompt and code is fluid.",
  "subtitleText": "Stay in prompt space as long as possible. Dip into code when you must."
}
```

---
