[Remotion]

# Section 7.4: Code Dissolve and Regenerate Loop

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:08 - 0:13

## Visual Description

Building directly from the PDD triangle (which remains visible in the background at reduced opacity), the code block in the center dissolves — characters scatter like particles — and then regenerates. New code appears, structurally different but functionally equivalent. A terminal strip at the bottom shows the loop: `pdd generate` → code appears → `pdd test` → `✓` → repeat.

The dissolve-regenerate cycle happens twice. Each regeneration produces slightly different code (variable names shift, implementation approach varies), but the test check mark always appears in green. The message is clear: the code is disposable, interchangeable. What matters is the mold (prompt + tests + grounding), not the plastic (code).

The triangle vertices continue their slow pulse throughout, anchoring the visual.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: 60px spacing, `#1E293B` at 0.03 opacity

### Chart/Visual Elements

#### Background Triangle (from 03)
- Same triangle from previous spec, but at 0.3 opacity
- Vertex glows reduced to 0.1 opacity
- Labels still visible but dimmed

#### Center Code Block
- Bounding box: 320x180px centered at (960, 470)
- Background: `#111827` at 0.85 opacity, 8px border-radius
- Code text: 13px JetBrains Mono
- Syntax colors: keywords `#C084FC`, strings `#86EFAC`, functions `#93C5FD`

#### Dissolve Particles
- Each character becomes a particle on dissolve
- Particles: 4x4px squares, color matches original syntax color
- Drift: random direction, 20-60px travel, 0.8→0 opacity fade
- Count: ~80-120 particles per dissolve

#### Terminal Strip
- Position: bottom of code block, (960, 600), 320x36px
- Background: `#000000` at 0.9 opacity
- Font: JetBrains Mono, 12px, `#4AD9A0` (teal/green)
- Prompt symbol: `$` in `#94A3B8`
- Check mark: `✓` in `#22C55E` (bright green)

### Animation Sequence

#### Cycle 1
1. **Frame 0-10 (0-0.33s):** Hold on existing code from previous spec
2. **Frame 10-30 (0.33-1s):** Code dissolves — characters scatter as particles outward
3. **Frame 30-50 (1-1.67s):** New code regenerates — characters type in rapidly (1 frame/char)
4. **Frame 50-55 (1.67-1.83s):** Terminal shows `$ pdd test` typing
5. **Frame 55-65 (1.83-2.17s):** Terminal shows `✓ All tests passed` — check mark in green

#### Cycle 2
6. **Frame 65-85 (2.17-2.83s):** Second dissolve — particles scatter again
7. **Frame 85-105 (2.83-3.5s):** Third code variant regenerates
8. **Frame 105-110 (3.5-3.67s):** Terminal shows `$ pdd test` again
9. **Frame 110-120 (3.67-4s):** Terminal shows `✓ All tests passed`

#### Hold
10. **Frame 120-150 (4-5s):** Final code holds, triangle glows brighten slightly, soft pulse

### Typography
- Code text: JetBrains Mono, 13px, Regular (400)
- Terminal text: JetBrains Mono, 12px, Regular (400)
- Check mark: 14px, Bold

### Easing
- Particle scatter: `easeOut(cubic)` per particle, randomized duration 10-20 frames
- Code type-in: linear, 1 frame per character
- Terminal type: linear, 2 frames per character
- Check mark pop: `easeOut(back)` over 8 frames (slight overshoot)
- Triangle glow brighten: `easeInOut(sine)` over 30 frames

## Narration Sync
> "Code is generated, verified, and"
> — closing_003 (7.82s – 10.94s)

> "The code is just plastic."
> — closing_004 (11.38s – 13.26s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Background triangle at reduced opacity */}
  <Sequence from={0} durationInFrames={150}>
    <PddTriangle opacity={0.3} glowOpacity={0.1} />
  </Sequence>
  {/* Cycle 1: dissolve + regenerate */}
  <Sequence from={0} durationInFrames={65}>
    <CodeBlock initialCode={codeV1} />
    <DissolveEffect triggerFrame={10} durationFrames={20} />
    <RegenerateEffect code={codeV2} startFrame={30} typeSpeed={1} />
    <TerminalStrip command="pdd test" result="✓ All tests passed" startFrame={50} />
  </Sequence>
  {/* Cycle 2: dissolve + regenerate */}
  <Sequence from={65} durationInFrames={55}>
    <DissolveEffect triggerFrame={0} durationFrames={20} />
    <RegenerateEffect code={codeV3} startFrame={20} typeSpeed={1} />
    <TerminalStrip command="pdd test" result="✓ All tests passed" startFrame={40} />
  </Sequence>
  {/* Final hold */}
  <Sequence from={120} durationInFrames={30}>
    <PddTriangle opacity={0.5} glowBrighten={true} />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "componentId": "dissolve_regenerate_loop",
  "durationFrames": 150,
  "fps": 30,
  "narrationSegments": ["closing_003", "closing_004"],
  "codeVariants": [
    {
      "version": 1,
      "lines": [
        "def calculate_total(items):",
        "    return sum(i.price for i in items)",
        "",
        "def apply_discount(total, pct):",
        "    return total * (1 - pct)"
      ]
    },
    {
      "version": 2,
      "lines": [
        "def get_total(cart_items):",
        "    total = 0",
        "    for item in cart_items:",
        "        total += item.price",
        "    return total"
      ]
    },
    {
      "version": 3,
      "lines": [
        "def compute_sum(products):",
        "    prices = [p.price for p in products]",
        "    return functools.reduce(",
        "        operator.add, prices, 0",
        "    )"
      ]
    }
  ],
  "terminalCommands": [
    { "command": "pdd test", "result": "✓ All tests passed" }
  ]
}
```

---
