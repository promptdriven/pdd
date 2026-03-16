[Remotion]

# Section 3.6: Prompt Capital — The Specification

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 14:38 – 15:00

## Visual Description
A visualization of the prompt as the specification layer of PDD. On the left, a compact prompt document (blue-bordered card, ~15 lines of natural language) is shown. On the right, the generated code it produces (~100 lines, gray code blocks). An animated ratio indicator shows "1:5 to 1:10" compression. The prompt card and code are connected by a transformation arrow. Two variations of generated code materialize from the same prompt — different implementations, same behavior — establishing that the contract is fixed but the code is flexible. Below, a context window comparison shows how natural-language prompts fit 5-10× more system context than raw code, with the MIT "89% improvement" stat called out.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: None

### Chart/Visual Elements
- **Prompt card (left):** Positioned at (280, 340), 360×320px
  - Background: `#1E293B`, border `#4A90D9` 2px, border-radius 8px
  - Header: "prompt.md" — `#4A90D9`, 14px, monospace, top-left with file icon
  - Content: 12 lines of stylized natural language text (horizontal bars of varying length)
  - Text bars: `#FFFFFF` at 0.3 opacity, 2px height, spaced 18px apart
  - Blue accent bar: 4px left border, `#4A90D9`
  - Size label below: "~300 tokens" — `#4A90D9`, 14px

- **Generated code (right):** Positioned at (1100, 250), 520×480px
  - Background: `#1E293B`, border `rgba(255,255,255,0.1)` 1px, border-radius 8px
  - Header: "module.py" — `#6B7C93`, 14px, monospace
  - Content: ~25 lines of stylized code (horizontal bars with indentation)
  - Code bars: `#6B7C93` at 0.3 opacity, 2px height, varied indentation
  - Size label below: "~2,500 tokens" — `#6B7C93`, 14px

- **Transformation arrow:** From prompt card right-edge → code left-edge
  - Curved arrow, `rgba(255,255,255,0.2)`, 2px, with `pdd generate` label at midpoint
  - Midpoint: animated spinning gear icon, `#4A90D9` at 0.3, 20px

- **Compression ratio indicator:** Centered at (690, 700)
  - Large text: "1 : 5–10" — `#FFFFFF`, 36px, bold
  - Subtitle: "Prompt is a fifth to a tenth the size of generated code" — `#94A3B8`, 14px
  - Visual: Small blue bar (50px) and large gray bar (350px) stacked, showing ratio

- **Dual code variants (appears mid-sequence):**
  - Two overlapping code cards at right side, offset 20px diagonally
  - Different internal line patterns but same overall shape
  - Label: "Different code. Same behavior." — `#FFFFFF` at 0.6, 16px
  - Green checkmark on each variant

- **Context advantage callout (bottom):** y=880
  - "Natural language is their deepest fluency" — `#4A90D9`, 16px
  - "MIT: +89% coding performance with natural language context" — `#FFFFFF` at 0.5, 15px
  - Source: "MIT, 2024" — `#94A3B8`, 13px

### Animation Sequence
1. **Frame 0–45 (0–1.5s):** Prompt card draws in — border traces clockwise, then interior text bars fade in top-to-bottom. "prompt.md" header appears. Synced with "Second: the prompt. Your specification of what you want."
2. **Frame 45–105 (1.5–3.5s):** Transformation arrow draws from prompt card to right. Spinning gear icon appears at midpoint. "pdd generate" label fades in below arrow.
3. **Frame 105–180 (3.5–6.0s):** Generated code card materializes on right — border draws, code lines fill in rapidly (2-frame stagger per line). "module.py" header appears. Size labels ("~300 tokens" and "~2,500 tokens") fade in below their respective cards.
4. **Frame 180–240 (6.0–8.0s):** Compression ratio indicator fades in center-bottom. "1 : 5–10" counter animates — the "1" appears first, then the ratio expands outward. Blue/gray comparison bars fill in. Synced with "A good prompt is a fifth to a tenth the size of the code it generates."
5. **Frame 240–330 (8.0–11.0s):** Code card duplicates — a second variant slides out from behind (offset 20px right, 20px down). Both have slightly different line patterns but identical overall dimensions. "Different code. Same behavior." label fades in with green checkmarks on each. Synced with "Notice something subtle: the exact implementation can vary. What's locked is the behavior."
6. **Frame 330–450 (11.0–15.0s):** Prompt card pulses blue. Label appears: "What and why, not how." — `#4A90D9`, 16px. The interior text bars of the prompt subtly recolor to blue at 0.15 opacity to emphasize it's natural language. Synced with "Think of the prompt as your header file. The generated code is the OBJ file."
7. **Frame 450–570 (15.0–19.0s):** Context advantage callout slides in from bottom. MIT stat counter animates 0→89%. "Natural language is their deepest fluency" appears first, then the MIT citation.
8. **Frame 570–660 (19.0–22.0s):** Hold. Prompt card has gentle blue glow pulse. All elements at final state.

### Typography
- File headers: JetBrains Mono, 14px, respective colors
- Size labels: Inter Regular, 14px, respective colors
- Compression ratio: Inter Bold, 36px, `#FFFFFF`
- Ratio subtitle: Inter Regular, 14px, `#94A3B8`
- "Different code" label: Inter Medium, 16px, `#FFFFFF` at 0.6 opacity
- "What and why" label: Inter Medium, 16px, `#4A90D9`
- Context callout: Inter Medium, 16px, `#4A90D9`
- MIT stat: Inter Regular, 15px, `#FFFFFF` at 0.5 opacity
- Source: Inter Regular, 13px, `#94A3B8`

### Easing
- Card border draw: `easeInOutCubic`
- Text bar fade-in: `easeOutQuad` (staggered, 2 frames per line)
- Arrow draw: `easeInOutCubic`
- Compression counter: `easeOutExpo` (800ms)
- Bar fill: `easeInOutCubic`
- Variant slide-out: `spring({ damping: 14, stiffness: 100 })`
- MIT counter: `easeOutExpo` (1s)
- Callout slide: `easeOutCubic`

## Narration Sync
> "Second: the prompt. Your specification of what you want."

> "The prompt doesn't define the walls — tests do that. The prompt defines what you're asking for and why."

> "Notice something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."

> "A good prompt is a fifth to a tenth the size of the code it generates. Think of the prompt as your header file. The generated code is the OBJ file. You're specifying what and why, not how."

> "This is why the context window advantage we talked about is so powerful. You're not stuffing code into a window and hoping the model figures it out. You're giving it natural language — its strongest modality."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Prompt card */}
    <Sequence from={0} durationInFrames={45}>
      <DrawOnCard
        x={280} y={340} width={360} height={320}
        borderColor="#4A90D9"
        header="prompt.md"
        lineCount={12}
      />
    </Sequence>

    {/* Transformation arrow */}
    <Sequence from={45} durationInFrames={60}>
      <TransformArrow
        from={{ x: 460, y: 500 }}
        to={{ x: 840, y: 490 }}
        label="pdd generate"
      />
    </Sequence>

    {/* Generated code card */}
    <Sequence from={105} durationInFrames={75}>
      <DrawOnCard
        x={1100} y={250} width={520} height={480}
        borderColor="rgba(255,255,255,0.1)"
        header="module.py"
        lineCount={25}
        lineColor="#6B7C93"
      />
    </Sequence>

    {/* Size labels */}
    <Sequence from={150} durationInFrames={30}>
      <FadeIn><SizeLabel text="~300 tokens" color="#4A90D9" x={280} y={680} /></FadeIn>
      <FadeIn><SizeLabel text="~2,500 tokens" color="#6B7C93" x={1100} y={750} /></FadeIn>
    </Sequence>

    {/* Compression ratio */}
    <Sequence from={180} durationInFrames={60}>
      <CompressionRatio ratio="1 : 5–10" x={690} y={700} />
    </Sequence>

    {/* Dual code variants */}
    <Sequence from={240} durationInFrames={90}>
      <DualVariants x={1100} y={250} offset={20} />
      <FadeIn>
        <Label text="Different code. Same behavior." y={760} />
      </FadeIn>
    </Sequence>

    {/* Context advantage callout */}
    <Sequence from={450} durationInFrames={120}>
      <SlideUp>
        <ContextCallout
          headline="Natural language is their deepest fluency"
          stat="+89% coding performance with NL context"
          source="MIT, 2024"
          y={880}
        />
      </SlideUp>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "prompt": {
    "filename": "prompt.md",
    "tokenCount": 300,
    "lineCount": 12,
    "color": "#4A90D9"
  },
  "generatedCode": {
    "filename": "module.py",
    "tokenCount": 2500,
    "lineCount": 100,
    "color": "#6B7C93"
  },
  "compressionRatio": {
    "min": 5,
    "max": 10,
    "display": "1 : 5–10"
  },
  "research": {
    "source": "MIT, 2024",
    "finding": "+89% coding performance with natural language context",
    "trainingRatio": "30× more natural language than code in training data"
  }
}
```

---
