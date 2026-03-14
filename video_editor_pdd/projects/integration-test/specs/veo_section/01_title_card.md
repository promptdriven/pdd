[title:]

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:07 – 0:08

## Visual Description
A clean title card introduces the "Veo Section" of the integration test video. The section title fades in from full transparency, centered on a deep navy background. A thin horizontal rule animates outward from the center beneath the title, followed by a subtitle that fades up. The card establishes the cinematic tone before transitioning to Veo-generated footage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0B1120)
- No grid lines

### Chart/Visual Elements
- **Title text:** "Veo Section" — centered horizontally and vertically offset 40% from top
- **Horizontal rule:** 2px solid line, color soft gold (#C9A84C), max width 400px, centered beneath title with 20px gap
- **Subtitle text:** "AI-Generated Cinematic Footage" — centered, 30px below the rule

### Animation Sequence
1. **Frame 0–10 (0–0.33s):** Title text fades in from opacity 0→1, slight translateY from +20px→0px
2. **Frame 10–18 (0.33–0.6s):** Horizontal rule expands from width 0→400px (center-anchored)
3. **Frame 18–26 (0.6–0.87s):** Subtitle fades in from opacity 0→1, translateY from +10px→0px
4. **Frame 26–30 (0.87–1.0s):** Hold — all elements fully visible

### Typography
- Title: Inter Bold, 56px, white (#FFFFFF)
- Subtitle: Inter Regular, 24px, muted silver (#A0AEC0)

### Easing
- Title fade: `easeOutCubic`
- Rule expand: `easeInOutQuad`
- Subtitle fade: `easeOutCubic`

## Narration Sync
> (No narration — title card plays before first narration line begins)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <TitleCard
    title="Veo Section"
    subtitle="AI-Generated Cinematic Footage"
    bgColor="#0B1120"
    accentColor="#C9A84C"
  />
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
