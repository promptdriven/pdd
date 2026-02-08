# Section 0.8: Title Card

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 1:50 - 2:00

## Visual Description

The title "Prompt-Driven Development" fades in over the regenerated code from the previous scene. The code remains visible but dims and recedes, becoming a textured backdrop. The title is centered, clean, and authoritative -- the thesis of the entire video. No narration. A beat of quiet confidence before the video's argument begins in earnest.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1E1E2E), continuous from previous scene
- The regenerated code from 01g is still on screen, serving as backdrop

### Animation Elements

1. **Background Code Dim**
   - The clean regenerated code from the previous scene remains visible
   - Code opacity reduces from 1.0 to 0.15 over the first 2 seconds
   - Terminal snippet in bottom-right fades out completely (opacity to 0)
   - Editor chrome (top bar, gutter) fades out
   - Cursor stops blinking and disappears
   - The code becomes a subtle texture -- legible if you squint, but not the focus

2. **Title Text: "Prompt-Driven Development"**
   - Position: centered horizontally and vertically
   - Font: Clean sans-serif (Inter, Helvetica Neue, or similar -- matches 3B1B title style)
   - Weight: 600 (semi-bold)
   - Size: ~72px
   - Color: White (#FFFFFF) with subtle warm tint (#F8F4F0)
   - Letter-spacing: 0.02em (slightly tracked for elegance)
   - Fade in with slight upward drift (20px translate-Y, settles to 0)

3. **Subtle Glow on Title**
   - Very faint blue glow (#4A90D9) behind the title text
   - Bloom radius: ~40px, opacity: 0.15
   - This is intentional: the PROMPT is where value resides, and the title carries that glow
   - The glow is subtle enough to feel atmospheric, not like a neon sign

4. **Optional Subtitle (if used)**
   - Text: could be empty / no subtitle for the cold open
   - If present: smaller text below, muted gray (#888)
   - This is a design decision -- the title alone may be stronger

5. **Vignette**
   - Soft radial vignette, darkening edges
   - Center bright, edges at ~85% darkness
   - Creates natural focus on the centered title

### Animation Sequence

1. **Frame 0-60 (0-2s):** Crossfade from code to title backdrop
   - Code opacity: 1.0 -> 0.15 (`easeInOutCubic`)
   - Editor chrome fades out: 1.0 -> 0.0
   - Terminal snippet fades out: 1.0 -> 0.0
   - Cursor disappears (no blink, just gone)
   - Vignette fades in: 0 -> target opacity

2. **Frame 30-90 (1-3s):** Title fades in
   - Title opacity: 0 -> 1 (`easeOutCubic`)
   - Title Y position: +20px -> 0px (`easeOutCubic`)
   - Subtle glow fades in slightly behind title
   - Overlaps with the code dimming -- title arrives as code recedes

3. **Frame 90-270 (3-9s):** Hold
   - Static composition: title centered, dimmed code behind, vignette framing
   - No animation -- pure stillness
   - This is the moment the viewer reads and absorbs the title
   - The silence (no narration) gives the title weight

4. **Frame 270-300 (9-10s):** Prepare for transition
   - Slight hold before the next section begins
   - No fade-out here -- the transition to Section 1 handles the exit
   - Title remains at full opacity at the cut point

### Title Typography Detail

```
Font:        Inter (or system sans-serif fallback)
Weight:      600
Size:        72px
Color:       #F8F4F0
Tracking:    0.02em
Line-height: 1.2
Alignment:   Center (horizontal and vertical)
Position:    Centered in frame, optionally shifted ~5% above true center
             (more visually balanced with dimmed code below)
```

### Code Structure (Remotion)

```typescript
const TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background code dims
  const codeDim = interpolate(
    frame,
    [0, 60],
    [1, 0.15],
    { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Editor chrome fades out
  const chromeFade = interpolate(
    frame,
    [0, 45],
    [1, 0],
    { extrapolateRight: 'clamp' }
  );

  // Terminal fades out
  const terminalFade = interpolate(
    frame,
    [0, 30],
    [1, 0],
    { extrapolateRight: 'clamp' }
  );

  // Title fade in
  const titleOpacity = interpolate(
    frame,
    [30, 90],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Title drift upward
  const titleY = interpolate(
    frame,
    [30, 90],
    [20, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Glow intensity
  const glowOpacity = interpolate(
    frame,
    [45, 90],
    [0, 0.15],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Vignette
  const vignetteOpacity = interpolate(
    frame,
    [0, 60],
    [0, 0.6],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
      {/* Dimmed code backdrop (from previous scene) */}
      <div style={{ opacity: codeDim }}>
        <CleanCodeBlock code={regeneratedCode} />
      </div>

      {/* Editor chrome (fading out) */}
      <div style={{ opacity: chromeFade }}>
        <EditorTopBar filename="user_parser.py" />
        <LineNumberGutter startLine={47} lineCount={15} />
      </div>

      {/* Terminal (fading out) */}
      <div style={{
        position: 'absolute',
        bottom: 40,
        right: 40,
        opacity: terminalFade,
      }}>
        <TerminalSnippet
          lines={[
            { text: '$ pdd generate user_parser', color: '#E0E0E0' },
            { text: 'Generating from prompt...', color: '#888' },
            { text: 'Done. (0.8s) \u2713', color: '#5AAA6E' },
          ]}
          style={{
            width: 300,
            padding: '8px 12px',
            backgroundColor: '#252535',
            borderRadius: 6,
            border: '1px solid #333',
            fontFamily: 'JetBrains Mono',
            fontSize: 12,
          }}
        />
      </div>

      {/* Vignette overlay */}
      <Vignette opacity={vignetteOpacity} />

      {/* Title with glow */}
      <div style={{
        position: 'absolute',
        top: '45%',
        left: '50%',
        transform: `translate(-50%, -50%) translateY(${titleY}px)`,
        opacity: titleOpacity,
        textAlign: 'center',
      }}>
        {/* Glow layer (behind text) */}
        <div style={{
          position: 'absolute',
          inset: -40,
          background: `radial-gradient(ellipse at center, rgba(74, 144, 217, ${glowOpacity}) 0%, transparent 70%)`,
          filter: 'blur(20px)',
          pointerEvents: 'none',
        }} />

        {/* Title text */}
        <h1 style={{
          fontFamily: 'Inter, -apple-system, sans-serif',
          fontWeight: 600,
          fontSize: 72,
          color: '#F8F4F0',
          letterSpacing: '0.02em',
          lineHeight: 1.2,
          margin: 0,
          position: 'relative', // Above glow layer
          textShadow: '0 2px 20px rgba(0,0,0,0.5)',
        }}>
          Prompt-Driven Development
        </h1>
      </div>
    </AbsoluteFill>
  );
};
```

### Easing
- Code dim: `easeInOutCubic` (smooth, gradual recession)
- Chrome/terminal fade: `easeOutCubic` (quick fade, gets out of the way)
- Title opacity: `easeOutCubic` (confident arrival)
- Title Y drift: `easeOutCubic` (settles into place)
- Glow: `easeOutCubic` (blooms gently)
- Vignette: `linear` (gradual, atmospheric)

## Narration Sync

No narration. This is a silent beat -- a title card.

The absence of narration is deliberate. The previous line ("So why are we still patching?") hangs in the air. The title appears as the answer: "Prompt-Driven Development." The viewer connects the question to the title without being told. The silence gives both the question and the answer room to breathe.

## Audio Notes
- Music: if using a score, this is where the main theme could begin -- a single sustained note or a gentle chord that establishes the tonal foundation for the rest of the video
- Alternatively: silence with a very faint low drone (continuation of ambient from previous scenes)
- No sound effects -- the title card is purely visual
- If a musical cue is used, it should begin around frame 30 (as the title starts to appear) and sustain through the hold

## Visual Style Notes
- This is the "poster frame" of the video -- should work as a standalone still image
- The dimmed code behind the title is thematic: the output (code) recedes, the concept (PDD) takes center stage
- The subtle blue glow on the title connects to the prompt color palette (#4A90D9) -- reinforcing that value resides in the specification, which is what PDD is about
- The title glow should NOT be heavy or flashy -- it is a whisper, not a shout
- White/warm-white text on dark background: high contrast, easy to read, authoritative
- 3Blue1Brown title cards are clean, centered, and mathematically balanced -- match that energy
- The code backdrop creates visual depth without competing for attention
- Frame composition: title at ~45% from top (slightly above true center) for visual weight balance

## Transition

This is the final shot of the Cold Open (Section 0). The transition to Section 1 (Economics) can be:
- **Hard cut** to the first chart/visual of the economics section
- **Fade to black** (brief, 0.5s) then fade into Section 1
- **Dissolve** from the title card into the opening frame of the economics argument

The title may reappear later in the video (bookend structure), so this is an introduction, not a one-time appearance.
