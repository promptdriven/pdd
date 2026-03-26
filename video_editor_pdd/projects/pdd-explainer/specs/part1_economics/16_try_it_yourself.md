[title:]

# Section 1.16: Try It Yourself — Handwritten Challenge Card

**Tool:** Title
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 7:35 - 7:40

## Visual Description

A closing challenge card for Part 1. The text "Try it yourself." appears in a handwritten-style font, as if someone wrote it on a whiteboard or notebook page. The style shifts deliberately from the clean Inter typography used throughout the section — it feels personal, direct, like a friend challenging you.

The background has a subtle paper or whiteboard texture, warmer than the navy-black of the data sections. The text appears with a slight hand-drawn animation — each letter traces on as if being written in real-time.

Below the main text, a small clean-font subtitle fades in: a URL or simple next-step prompt, depending on the video's call-to-action.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (slightly warmer than the chart backgrounds) with subtle paper texture overlay at 0.03
- Grid lines: none

### Chart/Visual Elements

#### Handwritten Text
- "Try it yourself." — handwritten font (e.g., Caveat, Patrick Hand, or similar), 64px, `#E2E8F0`
- Centered at (960, 480)
- Appears with stroke-draw animation, as if being handwritten

#### Underline
- Hand-drawn style underline below "yourself" — slightly wavy, `#2DD4BF` at 0.5, 2px
- Draws from left to right after text completes

#### Period
- The period at the end is slightly larger/bolder than expected — a deliberate design choice to emphasize finality

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background appears. Slight texture visible.
2. **Frame 30-90 (1-3s):** "Try it yourself." traces on letter by letter, handwritten style. ~3 frames per character.
3. **Frame 90-110 (3-3.67s):** Underline draws beneath "yourself".
4. **Frame 110-150 (3.67-5s):** Hold. The challenge sits on screen.

### Typography
- Main text: Caveat (or similar handwritten Google Font), 64px, `#E2E8F0`
- Underline: hand-drawn path, `#2DD4BF` at 0.5

### Easing
- Letter trace: `linear` — consistent writing speed for realism
- Underline draw: `easeOut(quad)` over 20 frames
- Background appear: `easeOut(quad)` over 20 frames

## Narration Sync
> (This card appears at the tail end of the section, after the final narration beat has ended. It's a visual punctuation mark.)

Falls after `part1_economics_033` ends at ~455.44s.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Paper texture overlay */}
    <TextureOverlay src="/textures/paper_subtle.png" opacity={0.03} />

    {/* Handwritten text */}
    <Sequence from={30}>
      <HandwrittenText
        text="Try it yourself."
        font="Caveat" size={64} color="#E2E8F0"
        x={960} y={480} align="center"
        charDelay={3} strokeAnimation />
    </Sequence>

    {/* Underline */}
    <Sequence from={90}>
      <HandDrawnLine
        from={[780, 510]} to={[1140, 510]}
        color="#2DD4BF" opacity={0.5} width={2}
        wavy amplitude={3} drawDuration={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "variant": "handwritten_challenge",
  "text": "Try it yourself.",
  "font": "Caveat",
  "backgroundColor": "#0F172A",
  "underlineColor": "#2DD4BF",
  "animation": "handwritten_trace",
  "narrationSegments": []
}
```

---
