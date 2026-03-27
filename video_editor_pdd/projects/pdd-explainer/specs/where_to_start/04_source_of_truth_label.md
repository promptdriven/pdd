[Remotion]

# Section 6.4: Source of Truth Shift — Regenerate & Compare

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:13 - 0:18

## Visual Description

A focused view of the transformation moment. The prompt file (`auth_handler.prompt.md`) sits on the right, glowing green. Below it, a compact test/regeneration loop plays:

1. A small terminal shows `pdd generate auth_handler.py` — code regenerates
2. Then `pdd test` — a checkmark appears: `✓ All tests pass`
3. A badge stamps onto the prompt file: "SOURCE OF TRUTH"

This is the validation beat — the moment when the viewer understands that the prompt has replaced the code as the authoritative artifact. The test passing is the proof.

The layout uses the same left/right split as the previous spec but zoomed into the prompt-file side. The gray code file is visible but receding in the background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Focus area: right two-thirds of screen

### Chart/Visual Elements

#### Prompt File (dominant)
- Position: center at (750, 350), 400x250px
- Border: `#5AAA6E`, 2.5px, 6px radius
- Header: "auth_handler.prompt.md" — Inter, 14px, semi-bold, `#5AAA6E`
- Content: 8-10 faint markdown lines, `#94A3B8` at 0.4
- Glow: `#5AAA6E` at 0.12, 20px blur

#### Regeneration Terminal (compact)
- Position: below prompt file at (750, 650), 500x80px
- Background: `#0D1117`, 4px radius
- Line 1: `$ pdd generate auth_handler.py` — JetBrains Mono, 13px, `#E2E8F0`
- Line 2: `$ pdd test` — JetBrains Mono, 13px, `#E2E8F0`
- Line 3: `✓ All tests pass` — JetBrains Mono, 13px, `#5AAA6E`

#### Gray Code File (background)
- Position: far left at (200, 400), 200x150px, `#94A3B8` at 0.1
- Label: "auth_handler.py" — Inter, 11px, `#64748B` at 0.3
- Fully desaturated, receding

#### Source of Truth Badge
- Rounded rectangle: `#5AAA6E` fill at 0.15, `#5AAA6E` 1.5px border, 20px radius
- Text: "SOURCE OF TRUTH" — Inter, 12px, bold (700), `#5AAA6E`, letter-spacing 2px
- Position: overlapping top-right of prompt file at (950, 260)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Prompt file is already visible (carried from previous spec). Terminal area fades in.
2. **Frame 15-45 (0.5-1.5s):** `pdd generate auth_handler.py` types in terminal.
3. **Frame 45-60 (1.5-2s):** Brief loading shimmer on prompt file — code is being regenerated.
4. **Frame 60-90 (2-3s):** `pdd test` types. Checkmark animates: `✓ All tests pass` in green.
5. **Frame 90-120 (3-4s):** "SOURCE OF TRUTH" badge scales in with slight bounce onto prompt file.
6. **Frame 120-150 (4-5s):** Hold. Badge and prompt glow together. Gray code recedes further.

### Typography
- File header: Inter, 14px, semi-bold (600), `#5AAA6E`
- Terminal: JetBrains Mono, 13px, `#E2E8F0`
- Test pass: JetBrains Mono, 13px, `#5AAA6E`
- Badge: Inter, 12px, bold (700), `#5AAA6E`, letter-spacing 2px

### Easing
- Terminal fade-in: `easeOut(quad)` over 15 frames
- Command type: linear, 3 frames per character
- Checkmark scale: `easeOut(back)` with overshoot, over 15 frames
- Badge scale-in: `easeOut(back)` over 20 frames
- Code recede: `easeInOut(cubic)` over 30 frames

## Narration Sync
> "When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001` (final portion, ~13.00s - 18.20s)

- **13.00s**: Terminal begins typing regenerate command
- **15.00s**: Test passes — checkmark appears
- **16.00s**: "SOURCE OF TRUTH" badge stamps on
- **18.20s** (seg 001 ends): Hold, badge glowing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Gray code file (receding) */}
    <GrayFile
      name="auth_handler.py"
      position={[200, 400]} size={[200, 150]}
      opacity={0.1}
    />

    {/* Prompt file (dominant) */}
    <PromptFile
      name="auth_handler.prompt.md"
      position={[750, 350]} size={[400, 250]}
      borderColor="#5AAA6E"
      glowRadius={20} glowOpacity={0.12}
    />

    {/* Regeneration terminal */}
    <Sequence from={15}>
      <FadeIn duration={15}>
        <CompactTerminal position={[750, 650]} width={500}>
          <Sequence from={0}>
            <TypeWriter text="pdd generate auth_handler.py"
              charDelay={3} color="#E2E8F0" />
          </Sequence>
          <Sequence from={30}>
            <TypeWriter text="pdd test"
              charDelay={3} color="#E2E8F0" />
          </Sequence>
          <Sequence from={45}>
            <ScaleIn duration={15} easing="easeOutBack">
              <Text text="✓ All tests pass"
                color="#5AAA6E" size={13} font="JetBrains Mono" />
            </ScaleIn>
          </Sequence>
        </CompactTerminal>
      </FadeIn>
    </Sequence>

    {/* Source of Truth badge */}
    <Sequence from={90}>
      <ScaleIn duration={20} easing="easeOutBack">
        <Badge
          text="SOURCE OF TRUTH"
          bgColor="#5AAA6E" bgOpacity={0.15}
          borderColor="#5AAA6E"
          textColor="#5AAA6E"
          position={[950, 260]}
          letterSpacing={2}
        />
      </ScaleIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "validation_sequence",
  "sequenceId": "regenerate_and_verify",
  "steps": [
    { "command": "pdd generate auth_handler.py", "description": "Regenerate code from prompt" },
    { "command": "pdd test", "description": "Run test suite" },
    { "result": "✓ All tests pass", "description": "Validation complete" }
  ],
  "badge": {
    "text": "SOURCE OF TRUTH",
    "target": "auth_handler.prompt.md"
  },
  "narrationSegments": ["where_to_start_001"]
}
```

---
