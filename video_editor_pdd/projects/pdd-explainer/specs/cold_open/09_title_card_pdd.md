[title:]

# Section 0.9: Title Card — Prompt-Driven Development

**Tool:** Title
**Duration:** ~2s
**Timestamp:** 0:16 - 0:18

## Visual Description
The clean regenerated code from spec 08 remains visible but dims to ~20% opacity. Over it, the title "Prompt-Driven Development" fades in — large, clean, centered. The text is white with a very subtle blue glow that pulses once, evoking the "regeneration" energy of the preceding beat. Below the main title, a thin horizontal rule fades in, followed by a subtle tagline or the video working title in smaller text. The background code provides texture without distraction.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E1E (continuing from code editor) with code at 20% opacity
- Overlay: Semi-transparent dark vignette (radial gradient from transparent center to #000000 at 60% opacity at edges)

### Chart/Visual Elements
- Title text: centered horizontally and vertically (960px, 480px)
- Horizontal rule: 200px wide, centered, 1px, #FFFFFF at 40% opacity
- Blue glow: box-shadow `0 0 40px rgba(79, 193, 255, 0.3)` on text, pulses once

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Background code dims from 100% → 20% opacity. Dark vignette fades in.
2. **Frame 6-24 (0.2-0.8s):** "Prompt-Driven Development" fades in (opacity 0 → 1) with slight scale-up (0.95 → 1.0).
3. **Frame 24-30 (0.8-1.0s):** Blue glow pulses: opacity 0 → 0.3 → 0. Single pulse.
4. **Frame 30-42 (1.0-1.4s):** Horizontal rule draws in from center outward (width 0 → 200px). Tagline fades in below.
5. **Frame 42-60 (1.4-2.0s):** Hold. All elements static.

### Typography
- Title: Inter Bold (or Outfit Bold), 72px, #FFFFFF, letter-spacing: 2px
- Tagline: Inter Regular, 22px, #AAAAAA, letter-spacing: 1px
- Horizontal rule: 1px solid #FFFFFF at 40% opacity

### Easing
- Code dim: `easeOutQuad`
- Title fade-in + scale: `easeOutCubic`
- Glow pulse: `easeInOutSine`
- Rule draw-in: `easeInOutQuad`

## Narration Sync
> "So why are we still patching?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  {/* Dim background code */}
  <Sequence from={0} durationInFrames={6}>
    <AnimateOpacity from={1} to={0.2}>
      <CodeEditor code={CLEAN_FUNCTION_CODE} theme="vscode-dark" />
    </AnimateOpacity>
  </Sequence>

  {/* Dark vignette overlay */}
  <FadeIn durationInFrames={6}>
    <RadialVignette color="#000000" opacity={0.6} />
  </FadeIn>

  {/* Title */}
  <Sequence from={6} durationInFrames={54}>
    <FadeIn durationInFrames={18}>
      <ScaleIn from={0.95} to={1.0} durationInFrames={18}>
        <Title
          text="Prompt-Driven Development"
          font="Inter Bold"
          size={72}
          color="#FFFFFF"
          letterSpacing={2}
          glowColor="rgba(79, 193, 255, 0.3)"
          glowPulseFrame={24}
        />
      </ScaleIn>
    </FadeIn>
  </Sequence>

  {/* Horizontal rule + tagline */}
  <Sequence from={30} durationInFrames={30}>
    <DrawLine width={200} color="#FFFFFF" opacity={0.4} durationInFrames={12} />
    <Sequence from={6}>
      <FadeIn durationInFrames={8}>
        <Subtitle text="Why You're Still Darning Socks" size={22} color="#AAAAAA" />
      </FadeIn>
    </Sequence>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "title": "Prompt-Driven Development",
  "tagline": "Why You're Still Darning Socks",
  "titleFont": "Inter Bold",
  "titleSize": 72,
  "titleColor": "#FFFFFF",
  "glowColor": "rgba(79, 193, 255, 0.3)",
  "backgroundCodeOpacity": 0.2,
  "vignetteOpacity": 0.6
}
```
