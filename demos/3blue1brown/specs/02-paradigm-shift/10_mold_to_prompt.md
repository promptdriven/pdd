# Section 2.10: Mold Morphs to Prompt

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 7:05 - 7:25

## Visual Description

The injection mold transforms into a glowing document labeled "PROMPT". The plastic part morphs into lines of code. The manufacturing metaphor becomes explicit: prompt = mold, code = plastic.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Full screen (no longer split)

### Morph Transformation

**Starting State:**
- Injection mold (3D-ish representation)
- Plastic part below/beside it
- Manufacturing context

**Ending State:**
- Glowing document labeled "PROMPT"
- Lines of code flowing below/beside it
- Software context

### Animation Elements

1. **Mold → Prompt Document**
   - Mold flattens into rectangular shape
   - Metallic texture → Paper/document texture
   - "PROMPT" label appears
   - Blue glow (#4A90D9) surrounds it

2. **Plastic Part → Code**
   - Part stretches into horizontal lines
   - Solid amber → Monospace text
   - Code syntax visible
   - Gray color (#A0A0A0)

3. **Context Shift**
   - Factory background fades
   - Abstract/digital background appears
   - Manufacturing → Software visual language

### Animation Sequence

1. **Frame 0-90 (0-3s):** Setup from previous section
   - Mold and part visible
   - Manufacturing context

2. **Frame 90-240 (3-8s):** Primary morph
   - Mold begins transforming
   - Shape flattens, rotates
   - Texture shifts to paper/screen
   - Part begins stretching into lines

3. **Frame 240-360 (8-12s):** Labels appear
   - "PROMPT" fades in on document
   - Code text becomes readable
   - Blue glow establishes on prompt

4. **Frame 360-480 (12-16s):** Relationship established
   - Arrow or flow indicator from prompt to code
   - "generates" label (optional)
   - Clear visual hierarchy

5. **Frame 480-600 (16-20s):** Hold on final state
   - Prompt glowing
   - Code present but not glowing
   - Ready for Part 3 concepts

### Visual Design: The Prompt Document

```
┌─────────────────────────────────┐
│           PROMPT                │ ← Title, centered
├─────────────────────────────────┤
│ Parse user IDs from untrusted   │
│ input. Return None on failure,  │
│ never throw. Handle unicode.    │
│                                 │
│ Requirements:                   │
│ - Validate format               │
│ - Sanitize input                │
│ - Return clean ID or None       │
└─────────────────────────────────┘
```

- Background: White or light blue
- Border: Subtle shadow
- Glow: Blue (#4A90D9) soft outer glow
- Text: Sans-serif, readable

### Visual Design: The Code

```
def parse_user_id(input_str):
    if not input_str:
        return None
    # Sanitize and validate
    clean = sanitize(input_str)
    if not validate_format(clean):
        return None
    return clean
```

- Background: None (transparent)
- Text: Monospace, syntax highlighted
- Color: Gray with subtle highlighting
- NO glow (value is in prompt, not code)

### Morph Technical Details

```typescript
const MoldToPromptMorph = ({ progress }) => {
  // Interpolate between mold shape and document shape
  const moldPath = "M0,0 L100,0 L100,80 L0,80 Z"; // Simplified
  const docPath = "M10,10 L190,10 L190,140 L10,140 Z";

  const currentPath = interpolatePath(moldPath, docPath, progress);

  // Interpolate colors
  const fillColor = interpolateColors(
    "#8A9BA8", // Steel gray
    "#FFFFFF", // White
    progress
  );

  // Interpolate glow
  const glowOpacity = progress * 0.6;
  const glowColor = "#4A90D9";

  return (
    <svg>
      <defs>
        <filter id="glow">
          <feGaussianBlur stdDeviation="10" />
        </filter>
      </defs>
      <path d={currentPath} fill={fillColor} />
      <path
        d={currentPath}
        fill={glowColor}
        opacity={glowOpacity}
        filter="url(#glow)"
      />
    </svg>
  );
};
```

### Easing

- Shape morph: `easeInOutCubic`
- Color transitions: `easeOutQuad`
- Label fade-in: `easeOutCubic`
- Glow appearance: `easeOutQuad`

## Narration Sync

> "This is Prompt-Driven Development."

This single line lands as the transformation completes and "PROMPT" is clearly visible.

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Mold to Prompt morph */}
  <Sequence from={90} durationInFrames={150}>
    <MorphAnimation
      from={<MoldVisualization />}
      to={<PromptDocument />}
    />
  </Sequence>

  {/* Plastic to Code morph */}
  <Sequence from={90} durationInFrames={150}>
    <MorphAnimation
      from={<PlasticPart />}
      to={<CodeLines />}
    />
  </Sequence>

  {/* Labels and glow */}
  <Sequence from={240}>
    <PromptLabel text="PROMPT" />
    <PromptGlow color="#4A90D9" />
  </Sequence>

  {/* Relationship indicator */}
  <Sequence from={360}>
    <FlowArrow from="prompt" to="code" />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- THE pivotal visual of Part 2
- Should feel like a revelation
- Manufacturing → Software connection made explicit
- 3Blue1Brown: elegant, mathematical, satisfying transformation

## Transition

Continues into Section 2.11 where the prompt pulses and generates code with tests as walls.
