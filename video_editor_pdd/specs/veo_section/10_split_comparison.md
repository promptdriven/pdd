[split:]

# Section 2.10: Split Comparison — Prompt vs. Output

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:27 - 0:30

## Visual Description
A split-screen layout comparing the text prompt (left) with the resulting Veo footage (right). The left panel shows the prompt text on a dark background, styled like a code editor or terminal. The right panel plays the corresponding ocean wave footage. A vertical divider with an animated "→" arrow icon emphasizes the input/output relationship. This visually demonstrates how Veo transforms text into video.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Black (#000000)

### Chart/Visual Elements
- Left panel: Dark code-editor style, 948x1080, positioned at X=0
  - Background: #1E1E2E (VS Code dark theme)
  - Prompt text block: Positioned center-left with 60px padding
  - Line numbers: Subtle, left gutter
  - Cursor blink: Blinking block cursor at end of prompt text
- Right panel: Ocean wave sunset clip, 948x1080, positioned at X=972
- Vertical divider: 24px wide zone at X=948-972
  - Background: linear gradient from #1E1E2E to transparent
  - Arrow icon: "→" symbol, 32px, #F59E0B, centered vertically in divider zone
- Left header: "PROMPT" small label, top-left of left panel
- Right header: "OUTPUT" small label, top-right of right panel

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Left panel slides in from left (-960 to 0). Right panel slides in from right (1920 to 972).
2. **Frame 15-45 (0.5-1.5s):** Prompt text types in character-by-character on left panel: "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion"
3. **Frame 30-40 (1-1.33s):** Arrow icon fades in and pulses once (scale 1.0 → 1.3 → 1.0).
4. **Frame 40-75 (1.33-2.5s):** Hold — prompt fully visible, footage plays on right.
5. **Frame 75-90 (2.5-3s):** Both panels slide outward. Left to X=-960, right to X=1920.

### Typography
- Prompt text: JetBrains Mono, 20px, #E2E8F0, line-height 1.6
- Line numbers: JetBrains Mono, 14px, #4A5568
- Panel headers: Inter SemiBold, 12px, #F59E0B, letter-spacing 3px, uppercase
- Arrow icon: Inter Bold, 32px, #F59E0B

### Easing
- Panel slide in/out: `easeOutCubic` / `easeInCubic`
- Text typing: `linear` (constant speed)
- Arrow pulse: `easeInOutSine`

## Narration Sync
> (No narration — visual demonstration beat)

## Code Structure (Remotion)
```typescript
<Sequence from={810} durationInFrames={90}>
  <SplitScreen>
    <LeftPanel background="#1E1E2E">
      <PanelHeader text="PROMPT" />
      <Sequence from={15}>
        <TypewriterText
          text="A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion"
          font="JetBrains Mono"
          speed={2}
        />
      </Sequence>
    </LeftPanel>
    <Divider>
      <Sequence from={30}>
        <ArrowIcon color="#F59E0B" />
      </Sequence>
    </Divider>
    <RightPanel>
      <PanelHeader text="OUTPUT" />
      <OffthreadVideo src={staticFile("veo/ocean_wave_sunset.mp4")} />
    </RightPanel>
  </SplitScreen>
</Sequence>
```

## Data Points
```json
{
  "promptText": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",
  "outputClip": "veo/ocean_wave_sunset.mp4",
  "leftBackground": "#1E1E2E",
  "accentColor": "#F59E0B"
}
```

---
