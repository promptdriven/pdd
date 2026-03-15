[title:]

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:08 – 0:10

## Visual Description
A cinematic title card introducing the Veo Section. A deep navy canvas fades in, followed by a gold horizontal rule that draws across the center. The title "Veo Section" types on above the rule in large white serif text, and a gold subtitle "AI-Generated Cinematic Footage" fades in below. The elements hold briefly before the card crossfades out.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: Dark navy `#0B1120`
- No grid lines

### Chart/Visual Elements
- **Horizontal Rule:** Centered gold line (`#C9A84C`), 200px wide, 2px thick, expanding from center outward
- **Title Text:** "Veo Section" — white `#FFFFFF`, centered above the rule
- **Subtitle Text:** "AI-Generated Cinematic Footage" — gold `#C9A84C`, centered below the rule

### Animation Sequence
1. **Frame 0–10 (0–0.33s):** Background fades in from black. Horizontal rule begins drawing outward from center point.
2. **Frame 10–25 (0.33–0.83s):** Horizontal rule reaches full 200px width. Title text fades in and slides up 10px into final position.
3. **Frame 25–40 (0.83–1.33s):** Subtitle text fades in with 0.3s delay after title. All elements hold.
4. **Frame 40–60 (1.33–2.0s):** Hold on full composition, then begin fade-to-black transition on last 10 frames.

### Typography
- Title: Inter Bold, 64px, `#FFFFFF`
- Subtitle: Inter Regular, 28px, `#C9A84C`, 90% opacity

### Easing
- Rule draw: `easeInOutCubic`
- Title fade/slide: `easeOutQuad`
- Subtitle fade: `easeOutQuad`

## Narration Sync
> (No narration during title card — visual-only intro)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0B1120' }}>
    <HorizontalRule color="#C9A84C" width={200} />
    <Sequence from={10}>
      <TitleText text="Veo Section" />
    </Sequence>
    <Sequence from={25}>
      <SubtitleText text="AI-Generated Cinematic Footage" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Veo Section",
  "subtitle": "AI-Generated Cinematic Footage",
  "background": "#0B1120",
  "accent": "#C9A84C"
}
```

---
