[title:]

# Section 0.8: PDD Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~2.5s (75 frames @ 30fps)
**Timestamp:** 0:16 - 0:17.5

## Visual Description

The title card fades in over the regenerated code from spec 07, creating a layered composition. The code remains visible underneath at reduced opacity — the clean, regenerated function serving as a visual foundation for the concept being named.

"Prompt-Driven Development" appears in large, confident typography, centered on screen. The text uses the PDD blue `#4A90D9` — the "new paradigm" color, contrasting with the amber `#D9944A` of patching/darning that dominated the split screen. A thin horizontal rule draws outward from center below the title.

The terminal overlay from spec 07 remains visible in the corner, reinforcing that this is a real tool, not just a concept. The overall effect is: you just watched code delete and regenerate — here's what that's called.

No subtitle. No explanation. Just the name. The rest of the video will explain.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` at base, with code from spec 07 visible at 0.12 opacity
- Grid lines: None

### Chart/Visual Elements

#### Code Underlay
- The regenerated code from spec 07 remains on screen
- Opacity dimmed to 0.12 — visible but not readable, serving as texture
- No animation — static

#### Title Text
- "Prompt-Driven Development" — Inter, 56px, bold (700), `#4A90D9` at 0.95
- Centered at x: 960, y: 490
- Letter-spacing: 1px
- Text-shadow: `0 0 40px rgba(74, 144, 217, 0.15)` — subtle blue glow

#### Horizontal Rule
- 160px wide, 2px tall, `#4A90D9` at 0.25
- Centered at x: 960, y: 545
- Draws from center outward (80px each direction)

#### Terminal Overlay (Persistent from spec 07)
- Same position: bottom-right, 360x80px
- Opacity reduces from 0.92 → 0.5 — it recedes but remains

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Code underlay dims from full opacity to 0.12. Semi-transparent dark overlay `#0D1117` at 0.88 fades in.
2. **Frame 10-35 (0.33-1.17s):** Title "Prompt-Driven Development" fades in with 12px upward slide. Blue glow blooms subtly.
3. **Frame 35-45 (1.17-1.5s):** Horizontal rule draws from center outward.
4. **Frame 45-75 (1.5-2.5s):** Hold. Title sits with authority. The name has been planted.

### Typography
- Title: Inter, 56px, bold (700), `#4A90D9` at 0.95, letter-spacing 1px
- No subtitle or additional text

### Easing
- Code dim overlay: `easeOut(quad)` over 10 frames
- Title fade-in + slide: `easeOut(cubic)` over 20 frames
- Blue glow bloom: `easeOut(quad)` over 25 frames
- Rule draw: `easeOut(cubic)` over 10 frames
- Terminal opacity reduce: `easeOut(quad)` over 15 frames

## Narration Sync
> "So why are we still darning code?"

Segment: `cold_open_006` (continuation — title appears as the question hangs)

- **0:16** ("So why are we"): Code dims, title begins to appear
- **0:17** ("still darning code?"): "Prompt-Driven Development" fully visible — the answer to the question

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={75}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Code underlay from spec 07 — dimmed */}
    <Sequence from={0}>
      <FadeIn duration={1}>
        <CodeBlock
          code={CLEAN_PROCESS_USER_DATA}
          language="typescript"
          fontSize={13}
          font="JetBrains Mono"
          theme="vscode-dark-plus"
          opacity={0.12}
        />
      </FadeIn>
    </Sequence>

    {/* Dark overlay to dim code */}
    <Sequence from={0}>
      <FadeIn duration={10}>
        <AbsoluteFill style={{ backgroundColor: 'rgba(13, 17, 23, 0.88)' }} />
      </FadeIn>
    </Sequence>

    {/* Title */}
    <Sequence from={10}>
      <SlideUp distance={12} duration={20}>
        <FadeIn duration={20}>
          <Text
            text="Prompt-Driven Development"
            font="Inter" size={56} weight={700}
            color="#4A90D9" opacity={0.95}
            letterSpacing={1}
            x={960} y={490} align="center"
            shadow="0 0 40px rgba(74, 144, 217, 0.15)"
          />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={35}>
      <DrawLine
        from={[880, 545]} to={[1040, 545]}
        color="#4A90D9" opacity={0.25}
        width={2} drawDuration={10} fromCenter
      />
    </Sequence>

    {/* Terminal overlay — fading to lower opacity */}
    <Sequence from={0}>
      <Interpolate from={0.92} to={0.5} duration={15}>
        {(opacity) => (
          <TerminalOverlay
            x={1540} y={980} width={360} height={80}
            bg="#161B22" bgOpacity={opacity}
            borderColor="#30363D" borderRadius={8}
          >
            <TerminalLine prompt="$" command="pdd generate"
              promptColor="#5AAA6E" cmdColor="#E2E8F0" />
            <TerminalLine
              text="✓ UserService.ts regenerated (18 lines, 3 tests passing)"
              color="#5AAA6E" statsColor="#94A3B8" />
          </TerminalOverlay>
        )}
      </Interpolate>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 0,
  "sectionLabel": null,
  "title": "Prompt-Driven Development",
  "titleColor": "#4A90D9",
  "titleSize": 56,
  "subtitle": null,
  "codeUnderlay": true,
  "codeUnderlayOpacity": 0.12,
  "terminalPersist": true,
  "terminalOpacity": 0.5,
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_006"]
}
```

---
