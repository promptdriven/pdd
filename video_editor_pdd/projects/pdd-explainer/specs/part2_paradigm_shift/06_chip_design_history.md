[veo:]

# Section 2.6: Chip Design History — 1980s Electronics Lab

**Tool:** Veo
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 9:18 - 9:25

## Visual Description

A cinematic transition scene: the factory floor dissolves to a 1980s electronics lab. An engineer hunches over a large drafting desk, drawing circuits by hand on a paper schematic. The desk is cluttered with reference books, a soldering iron stand, oscilloscope in the background. Fluorescent overhead lighting with a warm desk lamp providing focused illumination. The schematic page is dense with transistor symbols, resistor zigzags, and connecting wires. The engineer's hand moves deliberately, drawing one gate at a time.

The camera starts medium-wide showing the lab environment, then slowly pushes in to the schematic on the desk. As we get closer, the density of the hand-drawn circuit becomes overwhelming — hundreds, then thousands of tiny transistor symbols covering the paper. The hand slows down. The task is becoming impossible at this scale.

This establishes the parallel: manufacturing hit a scale wall → chip design hit the same wall.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: 1980s lab interior
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium-wide establishing → push-in to close-up on schematic
- Movement: Slow push-in, ~15% travel over 7 seconds
- Depth of field: starts moderate f/4.0, narrows to shallow f/2.0 as we push in
- Angle: over-the-shoulder, slightly elevated, looking down at desk

**Lighting**
- Key light: warm desk lamp, `#E8C87A`, from the left
- Fill: cool fluorescent overhead, `#B8C8D8`, low intensity
- Practical: oscilloscope green screen glow in background, `#3A8A3A` at 0.2
- Specular: pen tip catching desk lamp light
- Overall tone: warm foreground, cool background — era-appropriate color grade

**Subject**
- Engineer: male, 30s-40s, dress shirt with rolled sleeves, focused
- Drafting desk: large, tilted surface, covered in paper schematics
- Schematic: dense circuit diagram, hand-drawn in black/blue ink
  - Transistor symbols (BJT), resistor zigzags, capacitor plates
  - Connecting wires, junction dots
  - Growing denser toward the edges of the page
- Background: oscilloscope, soldering station, reference books, component bins
- Props: mechanical pencils, rulers, eraser shavings

**Character**
- The engineer is a recurring figure representing "the designer who hits scale limits"
- Same character referenced in later chip design scenes

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Fade in from the factory scene. Medium-wide shot of the 1980s lab. Fluorescent flicker. Oscilloscope glows.
2. **Frame 30-90 (1.0-3.0s):** Camera begins push-in. Engineer visible drawing on schematic. Hand moves steadily. Desk lamp catches pen strokes.
3. **Frame 90-150 (3.0-5.0s):** Camera reaches close-up on the schematic. Density of transistor symbols becomes visible. Hundreds of tiny gates. The hand is still drawing but slowing.
4. **Frame 150-180 (5.0-6.0s):** Tighter still on the paper. Thousands of symbols. The schematic is becoming impossibly dense. The hand pauses.
5. **Frame 180-210 (6.0-7.0s):** Hold on the overwhelming density. The scale problem is visually self-evident. Fade begins at frame 200.

### Typography
- None (pure B-roll footage)

### Easing
- Camera push-in: `easeInOut(cubic)` (accelerating toward the schematic)
- Fade-in: `easeOut(quad)`, 1s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Medium-wide shot of a 1980s electronics lab. An engineer in a dress shirt with rolled sleeves hunches over a large tilted drafting desk, hand-drawing circuit schematics with a mechanical pencil. The paper is dense with transistor symbols, resistor zigzags, and connecting wires in black ink. Warm desk lamp illumination from the left, cool fluorescent overhead lighting. An oscilloscope glows green in the background. Reference books and component bins on shelves. Camera slowly pushes in toward the schematic, revealing the overwhelming density of hand-drawn gates — hundreds of tiny symbols. The engineer's hand slows as the scale becomes impossible. Period-accurate 1980s laboratory. Cinematic, 24fps, warm-cool mixed lighting, era-appropriate color grade.
```

## Narration Sync

> "And it's not just plastics. The chip industry hit this exact wall — and I watched it happen."
> "In the 1980s, chip designers drew every gate by hand. When transistor counts hit tens of thousands, they couldn't keep up."

Segment: `part2_006`
Timing: 9:18 - 9:25

- **9:18** ("And it's not just plastics"): Lab establishing shot, factory dissolves
- **9:21** ("The chip industry hit this exact wall"): Engineer visible, drawing circuits
- **9:23** ("In the 1980s, chip designers drew every gate by hand"): Push-in on schematic density

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={210}>
  <VeoClip
    clipId="chip_design_1980s_lab"
    src="/clips/chip_design_1980s_lab.mp4"
    fit="cover"
  />
  {/* Fade in (crossfade from factory) */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={200} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "chip_design_1980s_lab",
  "characters": [
    {
      "id": "chip_engineer",
      "label": "Chip Engineer",
      "referencePrompt": "Male engineer, 30s-40s, dress shirt with rolled sleeves, 1980s electronics lab, hunched over drafting desk drawing circuit schematics by hand"
    }
  ],
  "camera": {
    "framing": "medium_wide_to_close_up",
    "movement": "push_in",
    "travelPercent": 15,
    "dof": "moderate_to_shallow",
    "angle": "over_shoulder_elevated"
  },
  "lighting": {
    "key": { "color": "#E8C87A", "position": "left", "type": "desk_lamp" },
    "fill": { "color": "#B8C8D8", "position": "overhead", "type": "fluorescent" },
    "practical": { "color": "#3A8A3A", "source": "oscilloscope" },
    "grade": "1980s_warm_cool_mixed"
  },
  "narrationSegments": ["part2_006"],
  "narrationTimingSeconds": { "start": 558.0, "end": 565.0 }
}
```

---
