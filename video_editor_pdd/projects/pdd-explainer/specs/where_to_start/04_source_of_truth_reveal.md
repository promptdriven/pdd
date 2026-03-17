[Remotion]

# Section 6.4: Source of Truth Reveal — Module Shelf Flip

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:39 - 23:47

## Visual Description

Eight module blocks are arranged in a horizontal shelf across the screen, representing a real codebase's components: "auth", "user", "cart", "pay", "ship", "inv", "log", "api". Each block is a small card with a code icon (`</>`) and its label beneath. All start in a uniform muted slate color — they look like ordinary code modules.

Then the first block ("auth") performs a satisfying 3D card flip. The front face (code icon, slate) rotates away to reveal the back face: a golden prompt document icon on a warm-tinted background. The flip is smooth and dimensional — a real Y-axis rotation. When auth lands face-up as a prompt, a counter appears above: "1 of 8 modules converted" with a thin progress bar (1/8 filled in gold). The remaining 7 modules dim slightly, emphasizing the single converted module as the starting point. The message is clear: start with one. Just one.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none

### Chart/Visual Elements

#### Module Shelf
- 8 modules, evenly spaced horizontally
- Shelf y-center: 520
- Module spacing: 200px center-to-center
- First module x: 160, Last module x: 1560 (centered distribution)

#### Module Card (default state)
- Size: 120w × 140h, rounded 10px
- Background: `#1E293B`
- Border: 1px `#334155` at 0.3
- Code icon: `</>` glyph, 28px, `#94A3B8` at 0.5, centered at card y-30
- Label: Inter, 12px, semi-bold (600), `#94A3B8` at 0.6, centered beneath card at y+85

#### Module Card (prompt state — back face of auth)
- Size: 120w × 140h, rounded 10px
- Background: `#1A1508` (warm dark)
- Border: 2px `#FBBF24` at 0.4
- Prompt icon: document glyph with golden glow, 28px, `#FBBF24`, centered at card y-30
- Glow: 10px Gaussian blur, `#FBBF24` at 0.12
- Label: Inter, 12px, semi-bold (600), `#FBBF24` at 0.8, centered beneath card

#### Module Labels (left to right)
- "auth", "user", "cart", "pay", "ship", "inv", "log", "api"

#### Progress Counter
- Position: centered at (960, 340)
- Text: "1 of 8 modules converted" — Inter, 16px, `#E2E8F0` at 0.7
- "1" is rendered in `#FBBF24`, bold (700)

#### Progress Bar
- Position: centered at (960, 370), 320w × 4h
- Track: `#1E293B`, rounded 2px
- Fill: 40w (1/8 of 320), `#FBBF24`, rounded 2px, left-aligned

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** All 8 module cards slide up from y+30 with staggered fade-in (5 frames stagger per card). All in default slate state.
2. **Frame 40-50 (1.33-1.67s):** Hold on the full shelf. All modules visible and uniform.
3. **Frame 50-100 (1.67-3.33s):** "auth" card performs 3D Y-axis flip. Front face (code) rotates 0°→90° (first 25 frames), then back face (prompt) rotates 90°→0° (next 25 frames). Card briefly thins at 90° perpendicular.
4. **Frame 100-130 (3.33-4.33s):** Auth card lands in prompt state. Golden glow pulse fires. Border illuminates.
5. **Frame 130-170 (4.33-5.67s):** Progress counter fades in above. "1" scales up with emphasis. Progress bar draws left-to-right with gold fill.
6. **Frame 170-210 (5.67-7s):** Remaining 7 modules dim to 0.4 opacity. Auth stays bright. The contrast is stark.
7. **Frame 210-240 (7-8s):** Hold on final state. Subtle ambient glow cycles on auth's golden border.

### Typography
- Module labels: Inter, 12px, semi-bold (600), `#94A3B8` at 0.6 (default) / `#FBBF24` at 0.8 (converted)
- Counter text: Inter, 16px, `#E2E8F0` at 0.7
- Counter number: Inter, 16px, bold (700), `#FBBF24`

### Easing
- Card slide-up: `easeOut(cubic)` from y+30, 20 frames each, stagger 5
- Card flip (front half): `easeIn(cubic)` rotateY 0°→90° over 25 frames
- Card flip (back half): `easeOut(cubic)` rotateY 90°→0° over 25 frames
- Glow pulse: `easeOut(quad)` opacity 0→0.25→0.12 over 20 frames
- Counter fade: `easeOut(quad)` over 15 frames
- Number scale: `easeOut(back(1.3))` over 12 frames
- Progress bar fill: `easeOut(cubic)` over 20 frames
- Module dim: `easeOut(quad)` opacity 1.0→0.4 over 25 frames

## Narration Sync
> "One module at a time."

Segment: `where_to_start_002`

- **23:39** ("One module"): Auth card begins its 3D flip
- **23:41** ("at a time"): Auth lands as prompt, counter appears — emphasis on the singular starting point

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Module shelf — 8 cards */}
    <Sequence from={0}>
      {['auth','user','cart','pay','ship','inv','log','api'].map((name, i) => (
        <Sequence key={name} from={i * 5}>
          <SlideIn direction="up" distance={30} duration={20}>
            <ModuleCard x={160 + i * 200} y={520}
              width={120} height={140}
              label={name} icon="code"
              bgColor="#1E293B" borderColor="#334155"
              iconColor="#94A3B8" labelColor="#94A3B8"
              id={`module_${name}`} />
          </SlideIn>
        </Sequence>
      ))}
    </Sequence>

    {/* 3D flip on auth card */}
    <Sequence from={50}>
      <CardFlip3D targetId="module_auth" duration={50}
        frontFace={{
          bgColor: '#1E293B', icon: 'code', iconColor: '#94A3B8'
        }}
        backFace={{
          bgColor: '#1A1508', icon: 'document',
          iconColor: '#FBBF24', borderColor: '#FBBF24',
          glow: { blur: 10, color: '#FBBF24', opacity: 0.12 }
        }}
      />
    </Sequence>

    {/* Progress counter */}
    <Sequence from={130}>
      <FadeIn duration={15}>
        <Text x={960} y={340} align="center" font="Inter" size={16}
          color="#E2E8F0" opacity={0.7}>
          <ScaleIn from={0.8} duration={12} easing="easeOut(back(1.3))">
            <Span text="1" color="#FBBF24" weight={700} />
          </ScaleIn>
          <Span text=" of 8 modules converted" />
        </Text>
      </FadeIn>

      {/* Progress bar */}
      <Sequence from={10}>
        <ProgressBar x={800} y={370} width={320} height={4}
          trackColor="#1E293B" fillColor="#FBBF24"
          progress={1/8} fillDuration={20} />
      </Sequence>
    </Sequence>

    {/* Dim remaining modules */}
    <Sequence from={170}>
      <AnimateOpacity targets={['user','cart','pay','ship','inv','log','api']}
        to={0.4} duration={25} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_shelf",
  "shelfId": "source_of_truth_reveal",
  "modules": [
    { "name": "auth", "converted": true },
    { "name": "user", "converted": false },
    { "name": "cart", "converted": false },
    { "name": "pay", "converted": false },
    { "name": "ship", "converted": false },
    { "name": "inv", "converted": false },
    { "name": "log", "converted": false },
    { "name": "api", "converted": false }
  ],
  "progress": { "converted": 1, "total": 8 },
  "convertedColor": "#FBBF24",
  "defaultColor": "#94A3B8",
  "backgroundColor": "#0F172A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
