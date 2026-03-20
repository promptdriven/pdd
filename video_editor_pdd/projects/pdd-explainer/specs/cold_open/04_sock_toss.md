[veo:]

# Section 0.4: Sock Toss — When Socks Got Cheap Enough

**Tool:** Veo (cinematic B-roll)
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:15 - 0:21

## Visual Description

Hard cut from the split screen. A modern-day person in casual clothes (jeans, t-shirt) sits on the edge of a bed in a clean, minimalist apartment. They hold up a sock with a visible hole in the toe. Brief beat — they shrug with a half-smile, toss the sock in a nearby wastebasket in one fluid motion. They reach to a bedside shelf and grab a fresh pair from a $4.99 multi-pack (visible price sticker). The camera follows the arc of the toss, then racks focus to the fresh pair. The mood is unbothered, practical — no sentimentality. Modern natural lighting: cool daylight from a window, clean white walls.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Aspect ratio: 16:9 native
- Color temperature: 5600K daylight

### Chart/Visual Elements
- **Subject:** Person in their 30s, casual modern clothing
- **Lighting:** Natural window light (key from camera-right), soft bounce fill
- **Depth of field:** Medium — f/4 equivalent, subject and immediate surroundings sharp
- **Camera:** Single shot, starts medium on the person, slight pan to follow sock arc, rack focus to fresh pair
- **Palette:** Cool neutrals — white `#F0F0F0`, light gray `#D1D5DB`, denim blue `#4B6A8A`
- **Key prop:** Multi-pack of socks with visible `$4.99` price tag, warm packaging colors

### Animation Sequence
1. **Frame 0-30 (0-1s):** Hard cut in. Person holds up holey sock, examines it briefly.
2. **Frame 30-60 (1-2s):** Shrug. The expression is "oh well" — no drama. Tosses sock toward wastebasket.
3. **Frame 60-100 (2-3.3s):** Camera follows the sock's arc. It lands in the wastebasket cleanly. Satisfying.
4. **Frame 100-150 (3.3-5s):** Person reaches to shelf, grabs fresh pair from multi-pack. Price tag `$4.99` is visible for at least 1 second.
5. **Frame 150-180 (5-6s):** Holds up the fresh pair with a casual "good enough" expression. The contrast with grandmother's careful repair is implicit.

### Typography
- None — pure cinematic footage

### Easing
- Camera pan: `easeInOut(sine)` — smooth follow
- Focus rack: `easeOut(quad)` — natural lens behavior

### Veo Prompt
```
Modern-day person sitting on the edge of a bed in a clean minimalist apartment. They hold up a sock with a visible hole in the toe, shrug casually with a half-smile, and toss it into a nearby wastebasket. They reach to a shelf and grab a fresh pair from a multi-pack of socks with a visible $4.99 price sticker. Natural daylight from a window, clean white walls, casual contemporary clothing. Camera follows the sock toss with a slight pan, then racks focus to the fresh pair. Medium shot, documentary style, 16:9, cinematic shallow depth of field. Unbothered, practical mood.
```

## Narration Sync
> "When socks got cheap enough... she stopped."

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_005` | "When socks got cheap enough..." | Frame 30 — as the sock is tossed |
| `cold_open_006` | "...she stopped." | Frame 120 — as fresh pair is grabbed |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <VeoClip
    clipId="sock_toss_modern"
    src="/assets/veo/sock_toss_modern.mp4"
    startFrom={0}
    playbackRate={1}
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "sock_toss_modern",
  "duration": 6,
  "frames": 180,
  "camera": "medium_tracking_rack_focus",
  "colorTemperature": "5600K",
  "era": "modern",
  "setting": "minimalist_apartment_bedroom",
  "props": ["holey_sock", "wastebasket", "sock_multipack", "price_tag_4_99"],
  "keyAction": "toss_and_replace",
  "narrationSegments": ["cold_open_005", "cold_open_006"]
}
```
