[Remotion]

# Section 0.8: Code Deletion and Regeneration

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:14 - 0:16

## Visual Description
Continuation of the code editor from spec 07. The entire patched function — all 30 lines — rapidly deletes from bottom to top in a cascading wipe, leaving an empty editor for a split second. Then clean, well-structured code regenerates line by line from top to bottom, flowing in smoothly like water filling a glass. The new code has no HACK comments, no TODO markers, no gutter annotations — it's pristine. In the bottom-right corner, a subtle terminal overlay appears showing `$ pdd generate ✓` with a green checkmark.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E1E (VS Code dark theme)
- Font: JetBrains Mono or Fira Code

### Chart/Visual Elements
- **Phase 1 (delete):** Lines disappear from bottom to top, each line fading out and sliding left slightly. Red-tinted glow on each line as it vanishes.
- **Phase 2 (empty):** Bare editor with just line numbers and cursor — brief stillness.
- **Phase 3 (regenerate):** Clean code types in top-to-bottom, 2-3 lines per frame, with a subtle blue glow trailing the generation front.
- **Terminal overlay:** Small (300x60px), bottom-right corner, 70% opacity background (#0D0D0D), monospace text showing `$ pdd generate ✓`

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** All 30 lines of patched code cascade-delete bottom-to-top. Each line fades out over 2 frames with a slight leftward slide (translateX 0 → -20px).
2. **Frame 15-18 (0.5-0.6s):** Empty editor. Cursor blinks once. Beat.
3. **Frame 18-48 (0.6-1.6s):** Clean code regenerates top-to-bottom. Lines appear 2-3 at a time with a blue trailing glow (#4FC1FF, 40% opacity). No HACK/TODO comments. Clean indentation.
4. **Frame 48-60 (1.6-2.0s):** Terminal overlay fades in (bottom-right): `$ pdd generate ✓` in green (#4EC9B0). Hold.

### Typography
- Code font: JetBrains Mono, 16px, #D4D4D4
- Terminal overlay: JetBrains Mono, 13px, #4EC9B0
- Terminal background: #0D0D0D at 70% opacity, 8px border-radius

### Easing
- Line deletion: `easeInQuad` (accelerating disappearance)
- Empty beat: static
- Line regeneration: `easeOutCubic` (decelerating, settling in)
- Terminal fade-in: `easeOutQuad`

## Narration Sync
> "Code just got that cheap."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  {/* Phase 1: Cascade delete */}
  <Sequence from={0} durationInFrames={15}>
    <CascadeDelete
      lines={PATCHED_FUNCTION_LINES}
      direction="bottom-to-top"
      perLineFrames={2}
      slideX={-20}
      glowColor="#FF4444"
    />
  </Sequence>

  {/* Phase 2: Empty beat */}
  <Sequence from={15} durationInFrames={3}>
    <EmptyEditor lineNumbers={30} />
    <BlinkingCursor line={1} column={1} color="#FFFFFF" />
  </Sequence>

  {/* Phase 3: Regenerate clean code */}
  <Sequence from={18} durationInFrames={30}>
    <CascadeGenerate
      lines={CLEAN_FUNCTION_LINES}
      direction="top-to-bottom"
      linesPerFrame={2}
      glowColor="#4FC1FF"
      glowOpacity={0.4}
    />
  </Sequence>

  {/* Terminal overlay */}
  <Sequence from={48} durationInFrames={12}>
    <FadeIn durationInFrames={6}>
      <TerminalOverlay
        text="$ pdd generate ✓"
        position="bottom-right"
        textColor="#4EC9B0"
        bgColor="#0D0D0D"
        bgOpacity={0.7}
      />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor_animation",
  "phases": [
    { "name": "cascade_delete", "direction": "bottom-to-top", "durationFrames": 15 },
    { "name": "empty_beat", "durationFrames": 3 },
    { "name": "cascade_generate", "direction": "top-to-bottom", "durationFrames": 30 },
    { "name": "terminal_overlay", "text": "$ pdd generate ✓", "durationFrames": 12 }
  ],
  "theme": "vscode-dark",
  "cleanCode": true,
  "terminalCommand": "pdd generate"
}
```
