[title:]
# Animation Section Title Card

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:00 - 0:05

## Visual Description
Animation Section appears as a crisp title card with immediate readability.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0A1628

### Animation Sequence
1. Frame 0-30: Establish the composition immediately.
2. Frame 30-90: Introduce the main motion or layout change.
3. Frame 90-150: Hold the final state clearly for rendering verification.

## Narration Sync
> "Animation Section appears as a crisp title card with immediate readability."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill />
</Sequence>
```

## Data Points
```json
{"series":[{"label":"A","value":1},{"label":"B","value":2}]}
```

<!-- ANNOTATION_UPDATE_START: f399f592-94d8-4233-b2a6-f5a60af87cca -->
## Annotation Update
Requested change: Change the main background color of this section to bright red (#FF0000). Find all background color values in the animation_section TSX component files under remotion/src/remotion/ and replace them with #FF0000.
Technical assessment: The animation_section currently uses dark navy/blue backgrounds across all three coded scene components. Scene 01 (title card) uses #0B1120 as the primary background with a #000000 outer fill and a #2E4A7A radial glow. Scene 02 (key visual) uses #0A1628. Scene 03 (split summary) uses #020617 as the main background with #0F172A and #111827 for the left/right panels. All of these need to be replaced with #FF0000 (bright red). Scenes 04 and 05 are Veo video clips rendered via OffthreadVideo and have no coded background to change.
- In AnimationSection01TitleCard/constants.ts, change COLORS.background from '#0B1120' to '#FF0000' and COLORS.glowCenter from '#2E4A7A' to '#FF0000' (or a red-tinted glow variant)
- In AnimationSection01TitleCard/AnimationSection01TitleCard.tsx, change the outer AbsoluteFill backgroundColor from '#000000' to '#FF0000'
- In animation_section_02_key_visual.tsx, change the AbsoluteFill backgroundColor from '#0A1628' to '#FF0000'
- In animation_section_03_split_summary.tsx, change the main backgroundColor from '#020617' to '#FF0000', and the left panel from '#0F172A' to '#FF0000' and the right panel from '#111827' to '#FF0000'
<!-- ANNOTATION_UPDATE_END: f399f592-94d8-4233-b2a6-f5a60af87cca -->
