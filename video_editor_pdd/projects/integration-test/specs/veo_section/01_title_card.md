[title:]

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~1.3s
**Timestamp:** 0:00 - 0:01

## Visual Description
A cinematic title card introducing the Veo Section. The screen fades from black to a deep ocean-blue gradient background. The section title "VEO SECTION" appears in bold uppercase, centered, with a subtle horizontal rule expanding outward from center beneath it. A thin subtitle reading "AI-Generated Video Integration" fades in below the rule. The overall tone is polished and cinematic, setting the stage for the Veo footage that follows.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Linear gradient from #0A1628 (top) to #1B3A5C (bottom)
- No grid lines

### Chart/Visual Elements
- **Title text:** "VEO SECTION" centered at y=440, white (#FFFFFF)
- **Horizontal rule:** 2px solid line, color #4DA8DA, starting from center expanding outward to 600px total width, positioned at y=500
- **Subtitle text:** "AI-Generated Video Integration" centered at y=540, light blue (#8EC8E8), opacity 0.85
- **Vignette overlay:** Radial gradient from transparent center to rgba(0,0,0,0.4) at edges

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Background fades in from black (opacity 0 → 1). Title text fades in and slides up 20px (opacity 0 → 1, translateY 20 → 0).
2. **Frame 10-22 (0.33-0.73s):** Horizontal rule expands from 0px to 600px width using `scaleX`. Subtitle fades in (opacity 0 → 1).
3. **Frame 22-38 (0.73-1.27s):** All elements hold steady. Subtle ambient glow pulse on the horizontal rule (opacity 0.8 → 1.0 → 0.8).

### Typography
- Title: Inter Bold, 72px, #FFFFFF, letter-spacing 12px
- Subtitle: Inter Regular, 24px, #8EC8E8, letter-spacing 4px, opacity 0.85

### Easing
- Title fade/slide: `easeOutCubic`
- Rule expansion: `easeInOutQuad`
- Subtitle fade: `easeOutQuad`

## Narration Sync
> (No narration during title card — serves as visual intro before narration begins)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={38}>
  <AbsoluteFill style={{ background: 'linear-gradient(180deg, #0A1628, #1B3A5C)' }}>
    <Sequence from={0}>
      <FadeIn duration={10}>
        <TitleText text="VEO SECTION" />
      </FadeIn>
    </Sequence>
    <Sequence from={10}>
      <ExpandingRule width={600} color="#4DA8DA" />
      <FadeIn duration={12}>
        <SubtitleText text="AI-Generated Video Integration" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "VEO SECTION",
  "subtitle": "AI-Generated Video Integration",
  "colors": {
    "gradientTop": "#0A1628",
    "gradientBottom": "#1B3A5C",
    "accent": "#4DA8DA",
    "subtitleColor": "#8EC8E8"
  }
}
```
