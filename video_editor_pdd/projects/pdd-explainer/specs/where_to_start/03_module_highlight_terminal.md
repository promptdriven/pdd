[Remotion]

# Section 6.3: Module Highlight & Terminal Command

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:10 - 0:15

## Visual Description

The dense legacy codebase from the previous shot is still visible, but now a single module — `auth_handler.py` — highlights with a blue selection glow. The other code panels dim to near-black. A terminal window slides up from the bottom of the screen, semi-transparent, showing the command being typed:

```
$ pdd update auth_handler.py
```

The command types character by character. On completion, the terminal shows output: `✓ Prompt generated: auth_handler.prompt.md`. A prompt file icon materializes next to the module — it glows a soft blue (`#60A5FA`), pulsing gently. The original code file simultaneously desaturates to gray, becoming visually subordinate. The prompt is the new source of truth; the code is now the artifact.

This is the pivotal visual moment — the inversion of value. What was authoritative (code) dims. What was derived (prompt) glows.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Dimmed Codebase
- Previous code panels at `#111827` at 0.3 (dimmed from 0.9)
- Code text: `#334155` at 0.2 (nearly invisible)
- Warning comments: `#D9944A` at 0.1 (nearly gone)

#### Highlighted Module
- `auth_handler.py` panel: full brightness, `#111827` at 0.95
- Selection glow: 12px blur, `#60A5FA` at 0.15, around panel border
- File tab `auth_handler.py`: active, 2px top border `#60A5FA`

#### Terminal Window
- Position: bottom-center, 700x180px, anchored at y: 880
- Background: `#0D1117` at 0.92
- Border: 1px `#30363D`, border-radius 8px
- Terminal header bar: 28px, `#161B22`, three dots (red/yellow/green circles, 8px)
- Prompt: `$` — JetBrains Mono, 13px, `#7EE787` at 0.8
- Command: `pdd update auth_handler.py` — JetBrains Mono, 13px, `#E2E8F0` at 0.9
- Output: `✓ Prompt generated: auth_handler.prompt.md` — JetBrains Mono, 12px, `#4ADE80` at 0.8

#### Prompt File Icon
- Position: next to highlighted module, offset right 20px
- Icon: rounded rectangle 40x50px, `#60A5FA` at 0.2 fill, `#60A5FA` at 0.6 stroke
- Label: `.prompt.md` — JetBrains Mono, 9px, `#60A5FA` at 0.7
- Glow: 16px blur, `#60A5FA` at 0.12, pulsing

#### Code-to-Artifact Shift
- Original code panel desaturates: filter grayscale(0.8), opacity drops to 0.4
- Label "artifact" — Inter, 10px, `#64748B` at 0.3, below code panel
- Label "source of truth" — Inter, 10px, `#60A5FA` at 0.5, below prompt icon

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Background panels dim. `auth_handler.py` panel brightens with selection glow. `easeOutCubic`.
2. **Frame 20-40 (0.67-1.33s):** Terminal window slides up from below viewport. `easeOutCubic`.
3. **Frame 40-80 (1.33-2.67s):** Command types character by character: `pdd update auth_handler.py` (1.5 frames per character).
4. **Frame 80-100 (2.67-3.33s):** Terminal output appears line by line. Green checkmark. `easeOutQuad`.
5. **Frame 100-120 (3.33-4s):** Prompt file icon materializes with scale-in (0 → 1) and glow. Code panel desaturates to gray. Labels appear. `easeOutBack`.
6. **Frame 120-150 (4-5s):** Hold. Prompt icon pulses. The inversion is visible — glowing prompt, gray code.

### Typography
- Terminal prompt: JetBrains Mono, 13px, `#7EE787` at 0.8
- Terminal command: JetBrains Mono, 13px, `#E2E8F0` at 0.9
- Terminal output: JetBrains Mono, 12px, `#4ADE80` at 0.8
- Prompt file label: JetBrains Mono, 9px, `#60A5FA` at 0.7
- Role labels: Inter, 10px, respective colors

### Easing
- Panel dim: `easeOut(cubic)` over 20 frames
- Terminal slide-up: `easeOut(cubic)` over 20 frames
- Command typing: `linear` at 1.5 frames per character
- Prompt icon scale-in: `easeOut(back)` over 20 frames
- Code desaturate: `easeInOut(quad)` over 20 frames
- Prompt glow pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "Start with one module. Generate its prompt. Add tests. Regenerate. Compare. When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001`

- **0:10** ("Start with one module"): `auth_handler.py` highlights, others dim
- **0:11** ("Generate its prompt"): Terminal slides up, command types
- **0:13** ("Add tests. Regenerate."): Terminal output appears, prompt file materializes
- **0:14** ("the prompt is your new source of truth"): Code grays out, prompt glows — inversion complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dimmed codebase */}
    <Sequence from={0}>
      <DimTransition duration={20} targetOpacity={0.3}>
        <CodebasePanels panels={panels} />
      </DimTransition>
    </Sequence>

    {/* Highlighted module */}
    <Sequence from={0}>
      <GlowHighlight color="#60A5FA" blur={12} opacity={0.15} duration={20}>
        <CodePanel
          file="auth_handler.py"
          highlighted={true}
          bgColor="#111827" bgOpacity={0.95}
        />
      </GlowHighlight>
    </Sequence>

    {/* Terminal window */}
    <Sequence from={20}>
      <SlideUp from={200} duration={20}>
        <TerminalWindow
          x={610} y={880} width={700} height={180}
          bgColor="#0D1117" borderColor="#30363D"
        >
          <Sequence from={20}>
            <TypeWriter
              text="pdd update auth_handler.py"
              font="JetBrains Mono" size={13}
              color="#E2E8F0" charDelay={1.5}
              prompt="$" promptColor="#7EE787"
            />
          </Sequence>
          <Sequence from={60}>
            <FadeIn duration={10}>
              <Text text="✓ Prompt generated: auth_handler.prompt.md"
                font="JetBrains Mono" size={12}
                color="#4ADE80" opacity={0.8} />
            </FadeIn>
          </Sequence>
        </TerminalWindow>
      </SlideUp>
    </Sequence>

    {/* Prompt file icon */}
    <Sequence from={100}>
      <ScaleIn from={0} to={1} duration={20}>
        <PromptFileIcon
          label=".prompt.md" color="#60A5FA"
          glowBlur={16} glowOpacity={0.12}
          pulseRate={30}
        />
      </ScaleIn>
    </Sequence>

    {/* Code desaturation */}
    <Sequence from={100}>
      <Desaturate amount={0.8} duration={20}>
        <FadeTo opacity={0.4} duration={20} />
      </Desaturate>
    </Sequence>

    {/* Role labels */}
    <Sequence from={110}>
      <FadeIn duration={15}>
        <Text text="artifact" font="Inter" size={10}
          color="#64748B" opacity={0.3} />
        <Text text="source of truth" font="Inter" size={10}
          color="#60A5FA" opacity={0.5} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_transformation",
  "chartId": "module_highlight_terminal",
  "highlightedModule": "auth_handler.py",
  "terminalCommand": "pdd update auth_handler.py",
  "terminalOutput": "✓ Prompt generated: auth_handler.prompt.md",
  "promptFile": "auth_handler.prompt.md",
  "transformation": {
    "code": { "role": "artifact", "color": "#64748B", "opacity": 0.4 },
    "prompt": { "role": "source_of_truth", "color": "#60A5FA", "opacity": 1.0 }
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_001"]
}
```

---
