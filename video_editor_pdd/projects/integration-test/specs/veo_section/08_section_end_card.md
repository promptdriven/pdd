[title:]

# Section 2.8: Section End Card

**Tool:** Remotion
**Duration:** ~0.8s
**Timestamp:** 0:15.8 – 0:16.6

## Visual Description
A closing title card for the Veo Section. The card displays a centered checkmark icon that scales in with a bounce, followed by the text "Veo Section Complete" and a thin horizontal rule. The design mirrors the opening title card's color palette (deep navy + gold accent) to bookend the section. All elements fade out together at the end to create a clean transition to the next section (or end of video).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0B1120)
- No grid lines

### Chart/Visual Elements
- **Checkmark icon (center, y: 380):**
  - Circle: 80px diameter, stroke 3px #10B981 (emerald), no fill
  - Checkmark path inside circle, stroke 3px #10B981
- **Title text (center, y: 500):**
  - "Veo Section Complete"
- **Horizontal rule (center, y: 550):**
  - 2px solid, color #C9A84C (gold), max width 300px
- **Subtitle (center, y: 590):**
  - "2 Veo clips · 3 Remotion overlays"

### Animation Sequence
1. **Frame 0–8 (0–0.27s):** Checkmark icon scales in from 0→1 with `easeOutBack` (bounce overshoot). Checkmark path draws via strokeDashoffset simultaneously
2. **Frame 8–14 (0.27–0.47s):** Title text fades in (opacity 0→1, translateY +15→0)
3. **Frame 14–18 (0.47–0.6s):** Horizontal rule expands from center (width 0→300px)
4. **Frame 18–22 (0.6–0.73s):** Subtitle fades in (opacity 0→1)
5. **Frame 22–24 (0.73–0.8s):** Hold — all elements visible. Then all elements fade out together (opacity 1→0) in the final 2 frames if needed for transition

### Typography
- Title: Inter Bold, 42px, white (#FFFFFF)
- Subtitle: Inter Regular, 20px, muted silver (#A0AEC0)

### Easing
- Checkmark scale: `easeOutBack`
- Checkmark draw: `easeInOutQuad`
- Title fade: `easeOutCubic`
- Rule expand: `easeInOutQuad`
- Subtitle fade: `easeOutCubic`

## Narration Sync
> (No narration — end card plays after final narration line concludes)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={24}>
  <AbsoluteFill style={{ backgroundColor: "#0B1120" }}>
    <AnimatedCheckmark
      x={960} y={380}
      size={80}
      color="#10B981"
      scaleInFrames={8}
    />

    <Sequence from={8}>
      <FadeInText
        text="Veo Section Complete"
        fontSize={42}
        color="#FFFFFF"
        y={500}
      />
    </Sequence>

    <Sequence from={14}>
      <HorizontalRule color="#C9A84C" width={300} y={550} />
    </Sequence>

    <Sequence from={18}>
      <FadeInText
        text="2 Veo clips · 3 Remotion overlays"
        fontSize={20}
        color="#A0AEC0"
        y={590}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Veo Section Complete",
  "subtitle": "2 Veo clips · 3 Remotion overlays",
  "stats": {
    "veo_clips": 2,
    "remotion_overlays": 3
  },
  "background": "#0B1120",
  "accent": "#C9A84C",
  "checkmark_color": "#10B981"
}
```

---
