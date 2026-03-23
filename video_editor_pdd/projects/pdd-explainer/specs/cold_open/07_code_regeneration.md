[Remotion]

# Section 0.7: Code Regeneration — The Delete and Rebuild

**Tool:** Remotion
**Duration:** ~1.5s (46 frames @ 30fps)
**Timestamp:** 0:16 - 0:17.5

## Visual Description

The payoff moment. The same patched function from spec 06 is on screen. Without warning, the entire function body selects (blue highlight sweeps down all 45 lines), then DELETES — the lines vanish upward in a fast, satisfying cascade. A brief flash of empty space. Then new, clean code REGENERATES line by line from the top, streaming in like an AI completion — but faster, cleaner, without any of the patch comments. The regenerated function is tight: 18 lines, no hacks, no TODOs, no workarounds.

In the bottom-right corner, a small terminal overlay fades in showing `$ pdd generate` with a green checkmark and `✓ UserService.ts regenerated (18 lines, 3 tests passing)`.

The whole sequence takes about 1.5 seconds. It's visceral — the accumulated weight of spec 06 is obliterated and replaced with something clean. The cursor settles at the end of the new function. No blink this time — it's done.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (IDE dark background, continuous from spec 06)
- Grid lines: None

### Chart/Visual Elements

#### Phase 1: Selection + Delete
- Selection highlight: `#264F78` at 0.4 (VS Code selection blue), sweeps from line 128 to line 171
- Delete animation: lines collapse upward — each line slides up and fades out, 1-frame stagger per line
- After delete: empty space between line 127 (`async function processUserData...`) and line 128 (closing bracket / next function)

#### Phase 2: Regeneration
- New code streams in line by line from the top of the function body
- Each line appears with a subtle left-to-right wipe (like AI completion typing)
- Code is clean TypeScript — proper types, clear variable names, no comments except one JSDoc
- Line color: standard VS Code Dark+ syntax highlighting
- Each line has a brief green flash `#5AAA6E` at 0.06 as it appears, then settles to normal

#### Phase 3: Terminal Overlay
- Position: bottom-right corner, 360x80px, 20px margin from edges
- Background: `#161B22` at 0.92, 8px border-radius
- Border: `#30363D` 1px
- Content:
  - `$` in `#5AAA6E`, `pdd generate` in `#E2E8F0` — JetBrains Mono, 11px
  - Second line: `✓ UserService.ts regenerated` in `#5AAA6E`, `(18 lines, 3 tests passing)` in `#94A3B8` — JetBrains Mono, 10px

#### Final State
- Clean function: 18 lines of TypeScript, no patch comments, properly typed
- Cursor: solid (no blink) at end of last line — `#E2E8F0` at 0.8
- Git gutter: all green (new/added) — `#5AAA6E` at 0.4

### Animation Sequence
1. **Frame 0-3 (0-0.1s):** Selection highlight sweeps down all 45 lines of the old function. Fast, deliberate.
2. **Frame 3-10 (0.1-0.33s):** Delete cascade — lines collapse upward with 1-frame stagger. The function body vanishes. Satisfying visual.
3. **Frame 10-12 (0.33-0.4s):** Brief empty space. One breath.
4. **Frame 12-35 (0.4-1.17s):** Regeneration — 18 new lines stream in, each with left-to-right wipe and green flash. ~1.3 frames per line.
5. **Frame 35-40 (1.17-1.33s):** Terminal overlay fades in at bottom-right. `pdd generate` with green checkmark.
6. **Frame 40-46 (1.33-1.5s):** Hold. Clean code. Green gutter. Terminal confirmation. Cursor solid.

### Typography
- Code: JetBrains Mono, 13px, VS Code Dark+ syntax colors
- Terminal text: JetBrains Mono, 11px (command), 10px (output)
- Terminal command: `#E2E8F0`, prompt `$` in `#5AAA6E`
- Terminal output: `#5AAA6E` (success), `#94A3B8` (stats)

### Easing
- Selection sweep: `linear` — fast, mechanical, 3 frames total
- Delete cascade: `easeIn(quad)` — accelerates as lines vanish upward
- Regeneration wipe: `easeOut(cubic)` per line — each line decelerates as it completes
- Green flash: `easeOut(expo)` — bright then fades quickly
- Terminal fade-in: `easeOut(quad)` over 5 frames

## Narration Sync
> "So why are we still darning code?"

Segment: `cold_open_006`

- **0:16** ("So why are we"): Function deletes — the old code vanishes
- **0:17** ("still darning code?"): New code regenerated, terminal shows `pdd generate` success

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={46}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Editor chrome (continuous from spec 06) */}
    <EditorTitleBar color="#161B22" />
    <FileTab name="UserService.ts" modified dotColor="#5AAA6E" />

    {/* Phase 1: Selection + Delete (frames 0-10) */}
    <Sequence from={0} durationInFrames={3}>
      <SelectionHighlight
        fromLine={128} toLine={171}
        color="#264F78" opacity={0.4}
        sweepDuration={3}
      />
    </Sequence>

    <Sequence from={3} durationInFrames={7}>
      <DeleteCascade
        fromLine={128} toLine={171}
        direction="up"
        staggerFrames={1}
        easing="easeInQuad"
      />
    </Sequence>

    {/* Phase 2: Regeneration (frames 12-35) */}
    <Sequence from={12}>
      <RegenerateLines
        lines={CLEAN_PROCESS_USER_DATA}
        lineCount={18}
        startLine={128}
        wipeDirection="left-to-right"
        flashColor="#5AAA6E"
        flashOpacity={0.06}
        framesPerLine={1.3}
        wipeEasing="easeOutCubic"
      />
    </Sequence>

    {/* Phase 3: Terminal overlay (frames 35-46) */}
    <Sequence from={35}>
      <FadeIn duration={5}>
        <TerminalOverlay
          x={1540} y={980} width={360} height={80}
          bg="#161B22" bgOpacity={0.92}
          borderColor="#30363D" borderRadius={8}
        >
          <TerminalLine prompt="$" command="pdd generate"
            promptColor="#5AAA6E" cmdColor="#E2E8F0" />
          <TerminalLine
            text="✓ UserService.ts regenerated (18 lines, 3 tests passing)"
            color="#5AAA6E" statsColor="#94A3B8" />
        </TerminalOverlay>
      </FadeIn>
    </Sequence>

    {/* Solid cursor at final position */}
    <Sequence from={35}>
      <Cursor line={145} column={2} color="#E2E8F0" opacity={0.8}
        width={2} blink={false} />
    </Sequence>

    {/* Green git gutter for all new lines */}
    <Sequence from={35}>
      <GitGutter
        lines={{ added: Array.from({ length: 18 }, (_, i) => 128 + i) }}
        colors={{ added: '#5AAA6E' }}
        opacity={0.4}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "animationType": "delete_and_regenerate",
  "file": "UserService.ts",
  "functionName": "processUserData",
  "deletePhase": {
    "lineRange": [128, 171],
    "lineCount": 44,
    "selectionColor": "#264F78",
    "cascadeDirection": "up",
    "durationFrames": 10
  },
  "regeneratePhase": {
    "lineCount": 18,
    "startLine": 128,
    "wipeDirection": "left-to-right",
    "flashColor": "#5AAA6E",
    "durationFrames": 23
  },
  "terminal": {
    "command": "pdd generate",
    "output": "✓ UserService.ts regenerated (18 lines, 3 tests passing)",
    "position": "bottom-right"
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_006"]
}
```

---
