# Section 2.4: Defect Discovered

**Tool:** Hybrid (Veo 3.1 + Remotion overlay)
**Duration:** ~10 seconds
**Timestamp:** 7:37 - 7:50

## Visual Description

A defect appears in one of the molded parts. Camera zooms in on the flaw. This sets up the key question: what do you do when there's a defect?

## Option A: Veo 3.1 Primary

### Veo 3.1 Prompt

```
Close-up shot of a plastic molded part with a visible defect.

SUBJECT:
- A simple plastic part (could be a cap, casing, or widget)
- Color: Amber/tan plastic
- Visible defect: crack, void, incomplete fill, or surface blemish
- Part is held or sits on inspection surface

ACTION:
1. Part comes into frame (conveyor or placed by hand)
2. Camera focuses on the defect
3. Slow zoom toward the flaw
4. Hold on the imperfection

ENVIRONMENT:
- Clean inspection area or quality control station
- Good lighting to reveal defect
- Neutral background (white or gray surface)

CAMERA:
- Macro or close-up lens
- Slow zoom in on defect
- Shallow depth of field (defect sharp, background soft)

LIGHTING:
- Bright, even lighting (like quality inspection)
- Possibly side-lighting to reveal surface defects

MOOD: Something is wrong. Attention drawn to the flaw.

DURATION: 8-10 seconds
NO PEOPLE (hands OK)
NO TEXT
```

## Option B: Remotion Animation

### Visual Description

Continuing from the stylized mold animation, one part ejects with a visible defect. The defect is highlighted with a red indicator.

### Animation Elements

1. **The Part**
   - Same style as Section 2.3
   - One part has visible flaw (crack, missing section, wrong shape)

2. **Defect Highlight**
   - Red circle or indicator appears
   - Pulsing animation
   - Label: "DEFECT" (optional)

3. **Zoom Effect**
   - Camera pushes in on the defective part
   - Other parts fade or blur
   - Focus narrows to the flaw

### Animation Sequence (Remotion)

1. **Frame 0-60 (0-2s):** Production continues from previous section
2. **Frame 60-120 (2-4s):** One part ejects with defect visible
3. **Frame 120-180 (4-6s):** Production pauses, highlight appears
4. **Frame 180-300 (6-10s):** Zoom in on defect, hold

## Hybrid Approach

Combine Veo footage with Remotion overlay:
- Veo: Real plastic part with defect
- Remotion: Red highlight circle, "DEFECT" label, zoom effect

### Overlay Specifications

```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Video layer */}
  <Video src="defect_closeup.mp4" />

  {/* Defect highlight */}
  <Sequence from={90}>
    <DefectHighlight
      position={{ x: defectX, y: defectY }}
      color="#D94A4A"
      pulseSpeed={30}
    />
  </Sequence>

  {/* Optional label */}
  <Sequence from={150}>
    <Label text="DEFECT" position="bottom-center" />
  </Sequence>
</Sequence>
```

## Narration Sync

> "And when there's a defect?"

This is a rhetorical setup. The answer comes in Section 2.5.

## Audio Notes

- Subtle "alert" sound when defect highlighted
- Production sounds stop or quiet
- Moment of tension

## Visual Style Notes

- The defect should be clearly visible but not grotesque
- Red highlight is clear but not overwhelming
- This is a PROBLEM, but a solvable one
- Sets up the key insight coming next

## Defect Types (Visual Options)

1. **Incomplete fill:** Part of the shape is missing
2. **Crack/fracture:** Visible line in the part
3. **Surface blemish:** Rough or incorrect texture
4. **Warping:** Part is bent or twisted
5. **Wrong dimension:** Part is too thick/thin

## Transition

Cut to engineer fixing the mold (Section 2.5) - the key insight.
