[Remotion]

# Section 3.4: Bug Found — Add a Wall, Regenerate

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 13:37 - 13:57

## Visual Description
An animated workflow showing the PDD approach to bug fixing. The mold cavity is visible with its existing test walls. A red "BUG" alert flashes on the generated code inside the cavity. Instead of patching the code, a new wall materializes in the mold — labeled with the bug condition. The code inside dissolves entirely, then regenerates from scratch, now conforming to the new constraint. A time-lapse follows: more bugs are found, more walls are added, and the mold becomes progressively more precise. Walls only accumulate — none disappear. This is the ratchet effect. A subtle terminal in the bottom-right shows `pdd bug user_parser` followed by `pdd fix user_parser`.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Mold Cavity:** Left-center, 650px wide x 320px tall, walls in `#D9944A` at 0.5 opacity. Pre-existing walls: 4 segments with labels from previous scene
- **Generated Code Block:** Inside cavity, represented as a filled rectangle `rgba(74,144,217,0.3)` with faint code-line texture (horizontal lines at 8px spacing, `rgba(255,255,255,0.05)`)
- **Bug Alert:** Red pulsing badge "BUG" — `#EF4444`, 36px bold, centered on code block. Red glow `rgba(239,68,68,0.3)` with 10px blur
- **New Wall:** Materializes on bottom-right of cavity, 20px thick, `#D9944A` at 0.7 opacity. Label: "handles null user_id" — 12px, `#D9944A`
- **Code Dissolve Effect:** The code block fragments into particles that drift upward and fade to 0 opacity
- **Code Regenerate Effect:** New code block materializes top-to-bottom within the cavity, `rgba(74,144,217,0.35)` — slightly brighter than before, respecting all walls including the new one
- **Ratchet Time-lapse Walls:** 4 additional walls appear in rapid succession (staggered 15 frames each), each with brief labels: "rejects empty string", "validates email format", "timeout at 100ms", "UTF-8 normalization"
- **Terminal (bottom-right):** Monospace panel, 350px wide x 100px tall, `rgba(0,0,0,0.4)` background
  - Line 1: `$ pdd bug user_parser` — `#94A3B8`, then "Creating failing test..." in `#22C55E`
  - Line 2: `$ pdd fix user_parser` — `#94A3B8`, then "All tests passing" in `#22C55E` with checkmark
  - Line 3 (time-lapse): `$ pdd test` with scrolling green checkmarks

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Mold cavity with existing walls and code block fade in
2. **Frame 30-70 (1.0-2.33s):** Bug alert — red "BUG" badge pulses in (scale 0→1.2→1.0) on the code block. Red glow emanates. Code block tints slightly red
3. **Frame 70-130 (2.33-4.33s):** New wall materializes — draws in from nothing, labeled "handles null user_id". Wall glows amber as it solidifies. Terminal shows `pdd bug user_parser` → "Creating failing test..."
4. **Frame 130-200 (4.33-6.67s):** Code block dissolves — fragments into upward-drifting particles that fade out. Cavity empties completely. The "BUG" badge dissolves with the code
5. **Frame 200-270 (6.67-9.0s):** New code regenerates — fills top-to-bottom, respecting all walls. Clean, no red tint. Terminal shows `pdd fix user_parser` → "All tests passing ✓"
6. **Frame 270-320 (9.0-10.67s):** Hold. New wall glows to confirm permanence. Text appears: "That bug can never occur again." — `#FFFFFF`, 20px, centered below cavity
7. **Frame 320-460 (10.67-15.33s):** Ratchet time-lapse — 4 additional walls materialize in quick succession (15-frame stagger). Each wall appears with a subtle "click" visual (brief white flash at attachment point). The mold becomes visibly more constrained. Terminal shows `pdd test` with scrolling checkmarks
8. **Frame 460-540 (15.33-18.0s):** Text below updates: "Tests only accumulate. The mold only gets more precise." — `#FFFFFF`, 20px
9. **Frame 540-600 (18.0-20.0s):** Hold at final state. All walls glow with ambient pulse

### Typography
- Bug Badge: Inter, 36px, bold (800), `#EF4444`
- Wall Labels: JetBrains Mono, 12px, regular (400), `#D9944A`
- Terminal Text: JetBrains Mono, 13px, regular (400)
- Emphasis Text: Inter, 20px, semi-bold (600), `#FFFFFF`

### Easing
- Bug badge pulse: `easeOut(back(1.5))`
- Wall materialize: `easeOut(cubic)`
- Code dissolve particles: `easeIn(quad)` for drift, `easeOut(quad)` for fade
- Code regenerate fill: `easeOut(cubic)`
- Ratchet wall stagger: `easeOut(back(1.2))` for each wall pop
- Terminal text: `linear` (typewriter feel)

## Narration Sync
> "Now watch what happens when you find a bug..."
> "...you don't patch the code. You add a wall."
> "That wall is permanent. That bug can never occur again — not in this generation, not in any future generation."
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Mold with existing code */}
  <Sequence from={0} durationInFrames={30}>
    <MoldCavity walls={existingWalls} />
    <CodeBlock opacity={0.3} />
  </Sequence>

  {/* Bug Alert */}
  <Sequence from={30} durationInFrames={40}>
    <BugBadge text="BUG" color="#EF4444" />
  </Sequence>

  {/* New Wall Materializes */}
  <Sequence from={70} durationInFrames={60}>
    <NewWall label="handles null user_id" color="#D9944A" />
    <Terminal lines={["$ pdd bug user_parser", "Creating failing test..."]} />
  </Sequence>

  {/* Code Dissolve */}
  <Sequence from={130} durationInFrames={70}>
    <CodeDissolve particleCount={60} direction="up" />
  </Sequence>

  {/* Code Regenerate */}
  <Sequence from={200} durationInFrames={70}>
    <CodeRegenerate direction="top-to-bottom" />
    <Terminal lines={["$ pdd fix user_parser", "All tests passing ✓"]} />
  </Sequence>

  {/* Permanence Text */}
  <Sequence from={270} durationInFrames={50}>
    <EmphasisText text="That bug can never occur again." y={750} />
  </Sequence>

  {/* Ratchet Time-lapse */}
  <Sequence from={320} durationInFrames={140}>
    <RatchetWalls
      walls={["rejects empty string", "validates email format", "timeout at 100ms", "UTF-8 normalization"]}
      stagger={15}
    />
    <Terminal lines={["$ pdd test", "✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓"]} scrolling={true} />
  </Sequence>

  {/* Final Text */}
  <Sequence from={460} durationInFrames={80}>
    <EmphasisText text="Tests only accumulate. The mold only gets more precise." y={750} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "existingWalls": [
    { "position": "left", "label": "null → None" },
    { "position": "bottom", "label": "empty string → ''" },
    { "position": "right", "label": "handles unicode" },
    { "position": "top-right", "label": "latency < 100ms" }
  ],
  "newWall": {
    "label": "handles null user_id",
    "position": "bottom-right"
  },
  "ratchetWalls": [
    "rejects empty string",
    "validates email format",
    "timeout at 100ms",
    "UTF-8 normalization"
  ],
  "terminal": {
    "commands": [
      { "cmd": "pdd bug user_parser", "output": "Creating failing test..." },
      { "cmd": "pdd fix user_parser", "output": "All tests passing ✓" },
      { "cmd": "pdd test", "output": "scrolling checkmarks" }
    ]
  }
}
```

---
