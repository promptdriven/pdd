[Remotion]

# Section 6.3: Module Highlight & Terminal Command

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 0:09 - 0:18

## Visual Description

From the zoomed-out codebase view, a single module (`auth_handler.py`) highlights with a green border glow. The rest of the codebase dims to near-darkness. A terminal panel slides up from the bottom of the screen, showing the command:

```
$ pdd update auth_handler.py
```

The command types out character by character. On completion, a prompt file (`auth_handler.prompt.md`) materializes next to the code file — it rises out of the existing code like an extraction, with glowing particle lines flowing from the code into the prompt file.

The code file then desaturates to gray (artifact), while the prompt file pulses with a warm green glow (source of truth). Two labels appear: "artifact" over the gray code, "source of truth" over the glowing prompt.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split layout: code file (left), prompt file (right), terminal (bottom)

### Chart/Visual Elements

#### Codebase Context (from previous spec)
- Zoomed-out codebase at 0.25 scale, `#94A3B8` at 0.15 — very faded background
- One module rectangle highlighted: `auth_handler.py`

#### Highlighted Module
- Border: `#5AAA6E`, 2px, 4px radius, glow: `#5AAA6E` at 0.2, 15px blur
- Label: "auth_handler.py" — Inter, 14px, semi-bold (600), `#5AAA6E`
- Position: center-left at (380, 400), 300x200px representation

#### Terminal Panel
- Background: `#0D1117`, slides up from bottom
- Height: 160px
- Prompt: `$` in `#5AAA6E`, command text in `#E2E8F0`
- Font: JetBrains Mono, 16px
- Cursor: blinking block `#5AAA6E`

#### Prompt File (materializing)
- Position: center-right at (1100, 400), 300x200px
- Border: `#5AAA6E`, 2px, 4px radius
- Header: "auth_handler.prompt.md" — Inter, 12px, `#5AAA6E`
- Content preview: faint markdown-like lines inside

#### Particle Flow
- 20-30 small particles (`#5AAA6E` at 0.6, 2px circles) flow from code file to prompt file
- Path: gentle arc from left to right
- Each particle fades on arrival

#### Labels
- "artifact" — Inter, 16px, italic, `#64748B` at 0.6, positioned below gray code file
- "source of truth" — Inter, 16px, semi-bold (600), `#5AAA6E`, positioned below glowing prompt file

### Animation Sequence
1. **Frame 0-30 (0-1s):** Module highlights with green border glow. Other modules dim to 0.15 opacity.
2. **Frame 30-60 (1-2s):** Terminal panel slides up from bottom. Cursor blinks.
3. **Frame 60-120 (2-4s):** Command types: `pdd update auth_handler.py` at 3 frames per character.
4. **Frame 120-150 (4-5s):** Command executes — brief processing indicator. Prompt file begins materializing on right.
5. **Frame 150-210 (5-7s):** Particle flow from code to prompt. Prompt file solidifies. Code file desaturates to gray.
6. **Frame 210-240 (7-8s):** Labels fade in: "artifact" and "source of truth".
7. **Frame 240-270 (8-9s):** Hold. Prompt glows steadily. Code is gray. Contrast is clear.

### Typography
- File labels: Inter, 14px, semi-bold (600), respective colors
- Terminal: JetBrains Mono, 16px, `#E2E8F0`
- Status labels: Inter, 16px, respective styles

### Easing
- Module highlight: `easeOut(quad)` over 20 frames
- Terminal slide-up: `easeOut(cubic)` over 25 frames
- Command type: linear, 3 frames per character
- Particle flow: `easeInOut(quad)` per particle, staggered 3-frame starts
- Desaturation: `easeInOut(cubic)` over 40 frames
- Label fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "Start with one module. Generate its prompt. Add tests. Regenerate. Compare. When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001` (second portion, ~9.00s - 18.20s)

- **9.00s**: Module highlights — "Start with one module"
- **11.00s**: Terminal types command — "Generate its prompt"
- **14.00s**: Prompt materializes, code grays — "the prompt is your new source of truth"
- **18.20s** (seg 001 ends): Labels visible, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Dimmed codebase background */}
    <CodebaseBackground opacity={0.15} scale={0.25} />

    {/* Highlighted module */}
    <Sequence from={0}>
      <ModuleHighlight
        name="auth_handler.py"
        position={[380, 400]}
        size={[300, 200]}
        borderColor="#5AAA6E"
        glowRadius={15} glowOpacity={0.2}
        animateDuration={20}
      />
    </Sequence>

    {/* Terminal panel */}
    <Sequence from={30}>
      <SlideUp distance={160} duration={25}>
        <TerminalPanel height={160} background="#0D1117">
          <TypeWriter
            text="pdd update auth_handler.py"
            font="JetBrains Mono" size={16}
            color="#E2E8F0" promptChar="$"
            promptColor="#5AAA6E"
            charDelay={3}
          />
        </TerminalPanel>
      </SlideUp>
    </Sequence>

    {/* Prompt file materializing */}
    <Sequence from={120}>
      <MaterializeFile
        name="auth_handler.prompt.md"
        position={[1100, 400]}
        size={[300, 200]}
        borderColor="#5AAA6E"
        duration={60}
      />
    </Sequence>

    {/* Particle flow: code → prompt */}
    <Sequence from={150}>
      <ParticleFlow
        from={[530, 400]} to={[950, 400]}
        count={25} color="#5AAA6E" opacity={0.6}
        particleSize={2} duration={60}
        staggerDelay={3}
      />
    </Sequence>

    {/* Code file desaturation */}
    <Sequence from={150}>
      <Desaturate target="auth_handler" duration={40} />
    </Sequence>

    {/* Labels */}
    <Sequence from={210}>
      <FadeIn duration={20}>
        <Text text="artifact" font="Inter" size={16}
          style="italic" color="#64748B" opacity={0.6}
          x={380} y={520} align="center" />
        <Text text="source of truth" font="Inter" size={16}
          weight={600} color="#5AAA6E"
          x={1100} y={520} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_transformation",
  "transformId": "module_to_prompt",
  "sourceFile": "auth_handler.py",
  "generatedFile": "auth_handler.prompt.md",
  "command": "pdd update auth_handler.py",
  "states": [
    { "id": "code_highlighted", "label": "Module selected" },
    { "id": "command_typed", "label": "PDD update executed" },
    { "id": "prompt_extracted", "label": "Prompt materialized" },
    { "id": "code_grayed", "label": "Code becomes artifact" },
    { "id": "prompt_glowing", "label": "Prompt is source of truth" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
