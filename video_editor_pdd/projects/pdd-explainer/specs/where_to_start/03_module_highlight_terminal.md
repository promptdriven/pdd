[Remotion]

# Section 6.3: Module Highlight & Terminal — `pdd update` Creates a Prompt

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 0:06 - 0:15

## Visual Description

The legacy codebase from the previous spec is still visible but now de-emphasized. A single module — `auth_handler.py` — highlights in the file tree and in the code wall, outlined with a glowing blue border.

A terminal panel slides up from the bottom of the frame, overlaying the lower third. The terminal shows the command being typed:

```
$ pdd update auth_handler.py
```

After the command executes, a new file materializes to the right of the code: `auth_handler.prompt.md`. The prompt file appears as a clean, glowing document — compact (5-6 visible lines), rendered with a blue-purple border and soft glow. It looks intentional, structured, authoritative.

Meanwhile, the original `auth_handler.py` code begins to dim — it's becoming an artifact. The prompt file glows brighter — it's becoming the source of truth.

A small animated arrow connects the code to the prompt: "extracted from →"

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme, inherited from Spec 02)

### Chart/Visual Elements

#### Module Highlight
- In file tree: `auth_handler.py` gets a blue highlight bar, `#4A90D9` at 0.15
- In code pane: the entire pane 1 gets a 2px border glow, `#4A90D9` at 0.3, rounded 6px
- Other code panes dim to 0.3 opacity

#### Terminal Panel
- Height: 200px, anchored to bottom
- Background: `#1A1A2E` at 0.95
- Border-top: `#334155`, 1px
- Prompt symbol: `$` — JetBrains Mono, 14px, `#10B981`
- Command text: `pdd update auth_handler.py` — JetBrains Mono, 14px, `#E2E8F0`
- Output line 1: `Analyzing auth_handler.py...` — `#64748B`
- Output line 2: `Generated auth_handler.prompt.md ✓` — `#10B981`

#### Prompt Document (materializes)
- Rounded rectangle: 400x280px, `#1E1E2E` fill, `#8B5CF6` 2px border
- Position: x: 1100, y: 200 (right side of frame)
- Label: `auth_handler.prompt.md` — Inter, 12px, `#8B5CF6`, top-left
- Body: 5-6 placeholder lines of spec text, Inter 12px, `#E2E8F0` at 0.8
- Glow: `#8B5CF6` at 0.12, 16px blur
- Materializes from particles converging inward

#### Extraction Arrow
- Curved arrow from code pane center-right to prompt document left edge
- Label: "extracted from →" — Inter, 11px, italic, `#64748B` at 0.6
- Arrow: `#4A90D9` at 0.3, 1.5px, dashed

### Animation Sequence
1. **Frame 0-30 (0-1s):** Code wall dims to 0.3 except pane 1. `auth_handler.py` highlights blue in file tree. Blue border glows around pane 1.
2. **Frame 30-60 (1-2s):** Terminal panel slides up from bottom. `$` prompt appears.
3. **Frame 60-100 (2-3.33s):** Command types character-by-character: `pdd update auth_handler.py` (1.5 frames per character).
4. **Frame 100-120 (3.33-4s):** Terminal output: "Analyzing auth_handler.py..." appears.
5. **Frame 120-160 (4-5.33s):** Prompt document materializes — particles converge from code pane into the document shape on the right. Glow blooms.
6. **Frame 160-180 (5.33-6s):** Terminal shows "Generated auth_handler.prompt.md ✓". Extraction arrow draws.
7. **Frame 180-220 (6-7.33s):** Original code in pane 1 begins fading to `#475569` at 0.3 (graying out). Prompt document glow intensifies.
8. **Frame 220-270 (7.33-9s):** Hold. Code = gray artifact. Prompt = glowing source of truth. The contrast is clear.

### Typography
- Terminal prompt: JetBrains Mono, 14px, `#10B981`
- Terminal command: JetBrains Mono, 14px, `#E2E8F0`
- Terminal output: JetBrains Mono, 13px, `#64748B` (analysis), `#10B981` (success)
- Prompt label: Inter, 12px, `#8B5CF6`
- Prompt body: Inter, 12px, `#E2E8F0` at 0.8
- Arrow label: Inter, 11px, italic, `#64748B` at 0.6

### Easing
- Code dim: `easeIn(quad)` over 30 frames
- Module highlight: `easeOut(cubic)` over 15 frames
- Terminal slide-up: `easeOut(back)` over 20 frames (slight overshoot)
- Command type: `linear`, 1.5 frames/character
- Particle converge: `easeIn(cubic)` over 40 frames
- Prompt glow bloom: `easeOut(quad)` over 20 frames
- Code gray-out: `easeIn(quad)` over 40 frames
- Arrow draw: `easeInOut(quad)` over 20 frames

## Narration Sync
> "PDD can create prompts from existing code. Start with one module. Generate its prompt. Add tests. Regenerate. Compare. When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001`

- **0:06** (6.00s): Module highlights — "Start with one module"
- **0:08** (8.00s): Terminal command types — "Generate its prompt"
- **0:10** (10.00s): Prompt materializes — "Add tests. Regenerate. Compare."
- **0:13** (13.00s): Code grays, prompt glows — "the prompt is your new source of truth"
- **0:15** (15.12s): Hold — segment ends

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>

    {/* Dimmed code wall from Spec 02 */}
    <Sequence from={0}>
      <AnimateOpacity from={0.7} to={0.3} duration={30}>
        <CodeWall panes={codePanes} />
      </AnimateOpacity>
    </Sequence>

    {/* Highlighted module — pane 1 */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <GlowBorder
          target="pane1" color="#4A90D9" opacity={0.3}
          width={2} radius={6} />
      </FadeIn>
    </Sequence>

    {/* File tree highlight */}
    <Sequence from={0}>
      <HighlightRow file="auth_handler.py" color="#4A90D9"
        opacity={0.15} duration={15} />
    </Sequence>

    {/* Terminal panel */}
    <Sequence from={30}>
      <SlideUp from={200} duration={20} easing="easeOut(back)">
        <TerminalPanel height={200} background="#1A1A2E">
          <Sequence from={30}>
            <TypeWriter
              text="pdd update auth_handler.py"
              prompt="$" promptColor="#10B981"
              font="JetBrains Mono" fontSize={14}
              charDelay={1.5} color="#E2E8F0" />
          </Sequence>
          <Sequence from={70}>
            <FadeIn duration={10}>
              <Text text="Analyzing auth_handler.py..."
                color="#64748B" font="JetBrains Mono" size={13} />
            </FadeIn>
          </Sequence>
          <Sequence from={130}>
            <FadeIn duration={10}>
              <Text text="Generated auth_handler.prompt.md ✓"
                color="#10B981" font="JetBrains Mono" size={13} />
            </FadeIn>
          </Sequence>
        </TerminalPanel>
      </SlideUp>
    </Sequence>

    {/* Prompt document materializes */}
    <Sequence from={120}>
      <ParticleConverge
        target={{ x: 1100, y: 200, width: 400, height: 280 }}
        source={{ x: 500, y: 300 }}
        duration={40} easing="easeInCubic"
      >
        <PromptDocument
          x={1100} y={200} width={400} height={280}
          label="auth_handler.prompt.md"
          borderColor="#8B5CF6" glowColor="#8B5CF6"
          glowOpacity={0.12} glowRadius={16}
          lines={5} font="Inter" fontSize={12}
        />
      </ParticleConverge>
    </Sequence>

    {/* Extraction arrow */}
    <Sequence from={160}>
      <DrawArrow
        from={{ x: 700, y: 340 }} to={{ x: 900, y: 340 }}
        color="#4A90D9" opacity={0.3} width={1.5} dashed
        label="extracted from →" labelColor="#64748B"
        drawDuration={20} />
    </Sequence>

    {/* Code gray-out */}
    <Sequence from={180}>
      <AnimateColor
        target="pane1_code" to="#475569" toOpacity={0.3}
        duration={40} easing="easeInQuad" />
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "interactive_demo",
  "command": "pdd update auth_handler.py",
  "targetModule": "auth_handler.py",
  "outputFile": "auth_handler.prompt.md",
  "phases": [
    { "id": "highlight", "frames": [0, 30], "description": "Module highlights in codebase" },
    { "id": "terminal", "frames": [30, 120], "description": "Terminal command executes" },
    { "id": "materialize", "frames": [120, 180], "description": "Prompt file materializes from code" },
    { "id": "shift", "frames": [180, 270], "description": "Code dims, prompt glows — source of truth shifts" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
