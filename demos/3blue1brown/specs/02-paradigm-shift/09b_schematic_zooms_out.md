# Section 2.9b: Schematic Zooms Out

**Tool:** Hybrid (Video + Remotion overlay)
**Duration:** ~20 seconds
**Timestamp:** 8:35 - 8:55

## Visual Description

The hand-drawn schematic zooms out. Hundreds of transistors. Then thousands. The engineer's hand slows down. The schematic becomes impossibly dense. This visualizes the scaling wall that forced the industry to move from manual schematics to hardware description languages.

## Option A: Video Primary

### Video Prompt

```
Continuation of 1980s electronics lab scene. Focus shifts entirely to the
schematic paper on the drafting desk.

SUBJECT:
- Hand-drawn circuit schematic, increasingly dense
- Engineer's hand drawing with mechanical pencil, gradually slowing
- The schematic fills with transistor symbols, wires, connection points
- Paper becomes overwhelmingly crowded with circuit elements

ACTION:
1. (0-5s) Engineer drawing at steady pace, schematic partially filled
2. (5-10s) Camera slowly zooms out, revealing more of the schematic
3. (10-15s) The full page is visible -- densely packed with circuits
4. (15-20s) Engineer's hand slows, hesitates, stops. The scale is overwhelming.

CAMERA:
- Starts close on the hand and pencil
- Slowly, continuously zooms out / pulls back
- Reveals the enormous scope of the schematic
- Ends at wide view of the entire desk covered in circuit drawings

LIGHTING:
- Same as previous section (warm drafting lamp)
- As zoom widens, overhead fluorescents become more visible

MOOD: Mounting realization. The task is becoming impossible. Human limits reached.

DURATION: 20 seconds
NO DIALOGUE
```

## Option B: Remotion Overlay

### Overlay Elements

Remotion overlays amplify the scaling problem visually:

1. **Transistor Counter**
   - Running count in corner that accelerates
   - Teal text (#2AA198) on semi-transparent dark background
   - Monospace font (JetBrains Mono)
   - Count: 100 ... 500 ... 1,000 ... 5,000 ... 10,000 ... 50,000

2. **Density Heat Map (Optional)**
   - Subtle color overlay showing density of components
   - Regions go from cool (sparse) to warm (impossibly dense)
   - Reinforces the visual of overwhelming complexity

3. **"Couldn't Scale" Indicator**
   - At the end, when the hand stops: amber (#D9944A) pulse or label
   - Connects to the abstraction timeline motif

### Animation Sequence (Overlay)

1. **Frame 0-90 (0-3s):** Counter starts, ticking slowly
   - "100 transistors" ... "200" ...
   - Engineer still drawing at normal pace

2. **Frame 90-210 (3-7s):** Counter accelerates with zoom-out
   - "500" ... "1,000" ... "2,000"
   - Zoom reveals more schematic area
   - Counter font size stays constant as schematic shrinks

3. **Frame 210-420 (7-14s):** Counter races ahead
   - "5,000" ... "10,000" ... "25,000"
   - Full schematic visible, impossibly dense
   - Counter acceleration conveys exponential growth

4. **Frame 420-540 (14-18s):** Hand slows, counter still climbing
   - "50,000" ... counter slows with the hand
   - Tension: the human cannot keep up

5. **Frame 540-600 (18-20s):** Hand stops
   - Counter freezes or blinks
   - Brief pause -- the wall is hit

### Overlay Specifications

```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Video layer */}
  <Video src="schematic_zooms_out.mp4" />

  {/* Transistor counter */}
  <Sequence from={0} durationInFrames={540}>
    <TransistorCounter
      startCount={100}
      endCount={50000}
      easing="easeInExpo"
      position="top-right"
      color="#2AA198"
      backgroundColor="rgba(30, 30, 46, 0.7)"
      fontSize={24}
      fontFamily="JetBrains Mono"
      label="transistors"
    />
  </Sequence>

  {/* Counter freeze/blink when hand stops */}
  <Sequence from={540} durationInFrames={60}>
    <TransistorCounter
      count={50000}
      blinking={true}
      position="top-right"
      color="#D9944A"
      fontSize={24}
      fontFamily="JetBrains Mono"
    />
  </Sequence>
</Sequence>
```

### Counter Component

```typescript
const TransistorCounter = ({
  startCount,
  endCount,
  easing,
  progress, // 0-1
  blinking,
  color,
  label,
}) => {
  const frame = useCurrentFrame();

  const count = blinking
    ? endCount
    : Math.round(
        interpolate(progress, [0, 1], [startCount, endCount], {
          easing: Easing.bezier(0.25, 0.1, 0.25, 1),
        })
      );

  const opacity = blinking
    ? Math.sin(frame * 0.3) > 0 ? 1 : 0.3
    : 1;

  return (
    <div style={{
      position: 'absolute',
      top: 40,
      right: 40,
      padding: '12px 20px',
      borderRadius: 8,
      backgroundColor: 'rgba(30, 30, 46, 0.7)',
      fontFamily: 'JetBrains Mono',
      fontSize: 24,
      color,
      opacity,
    }}>
      {count.toLocaleString()} {label}
    </div>
  );
};
```

## Narration Sync

> "In the 1980s, chip designers drew every gate by hand. When transistor counts hit tens of thousands, they couldn't keep up. So in 1985, they moved up--from schematics to Verilog. A hardware description language. You described what you wanted the chip to do, and a synthesis tool generated the gates."

This is a longer narration block. Key sync points:
- "drew every gate by hand" -- engineer is drawing, counter ticking
- "tens of thousands" -- counter reaches high numbers, schematic impossibly dense
- "couldn't keep up" -- hand slows and stops
- "moved up--from schematics to Verilog" -- transition to Section 2.9c begins

## Audio Notes

- Pencil scratching sounds continue from previous section
- Scratching pace slows as hand slows
- Subtle tension in music bed -- building unease
- Silence beat when hand stops -- the wall moment
- No dramatic sting; the visual tells the story

## Visual Style Notes

- The zoom-out is the key visual technique: reveals scale that was hidden
- Should feel like a "powers of ten" moment -- each zoom level shows more complexity
- The hand slowing is the emotional beat: human limits are real
- Counter provides concrete numbers for the narration
- Warm/analog color grading continues from previous section
- 3Blue1Brown aesthetic: let the mathematics (exponential growth) speak through the visual

## Transition

The impossibly dense schematic dissolves into clean Verilog code in Section 2.9c, representing the industry's solution to the scaling wall.
