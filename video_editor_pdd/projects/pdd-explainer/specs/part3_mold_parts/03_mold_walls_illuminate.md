[Remotion]

# Section 3.3: Mold Walls Illuminate — Test Labels

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:58 - 1:08

## Visual Description

The mold cross-section from the previous shot transitions: the nozzle and cavity dim, and the walls illuminate fully. The camera conceptually "zooms" into the wall region. Each wall segment receives a label that represents a specific test constraint:

- Wall segment 1: `null → None`
- Wall segment 2: `empty string → ''`
- Wall segment 3: `handles unicode`
- Wall segment 4: `latency < 100ms`

The labels appear one by one, attached to distinct wall segments along the left and right interior. Each label uses monospace font to suggest code/test assertions. As each label appears, the corresponding wall segment brightens, emphasizing that every test is a physical constraint in the mold.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold Structure (inherited from 02)
- Outer shell: `#334155` stroke, 3px
- Walls: `#4A90D9` glow active, other regions dimmed to 0.05 opacity

#### Wall Labels
- Font: JetBrains Mono, 14px, regular (400), `#CDD6F4`
- Background pill: `#4A90D9` at 0.15, rounded 4px, 8px horizontal padding
- Connector: 1px dashed line from wall segment to label, `#4A90D9` at 0.3
- Labels positioned alternating left and right of the mold walls

#### Wall Segments
- Four distinct segments along the interior walls
- Each segment: 3px wide, `#4A90D9`, glow increases from 0.2 to 0.5 when its label appears

### Animation Sequence
1. **Frame 0-30 (0-1s):** Transition from full mold view. Nozzle and cavity dim. Walls brighten. Subtle zoom (scale 1.0 → 1.15 on mold).
2. **Frame 30-75 (1-2.5s):** Wall segment 1 brightens. Label `null → None` fades in on the left with connector line drawing.
3. **Frame 75-120 (2.5-4s):** Wall segment 2 brightens. Label `empty string → ''` fades in on the right.
4. **Frame 120-165 (4-5.5s):** Wall segment 3 brightens. Label `handles unicode` fades in on the left.
5. **Frame 165-210 (5.5-7s):** Wall segment 4 brightens. Label `latency < 100ms` fades in on the right.
6. **Frame 210-300 (7-10s):** Hold. All four wall segments glowing, all labels visible. The walls are dense with constraints.

### Typography
- Wall labels: JetBrains Mono, 14px, regular (400), `#CDD6F4`
- Label pills: `#4A90D9` at 0.15, border-radius 4px

### Easing
- Zoom: `easeInOut(cubic)` over 30 frames
- Segment brighten: `easeOut(quad)` over 15 frames
- Label fade-in: `easeOut(quad)` over 20 frames
- Connector draw: `easeOut(quad)` over 15 frames

## Narration Sync
> "First: tests. Tests are the walls of your mold. Each test is a constraint. A boundary the generated code cannot cross."

Segment: `part3_mold_parts_006`

- **58.30s** (seg 006): Walls brighten, "First: tests"
- **61.0s**: First label appears on "walls of your mold"
- **64.0s**: Labels continue appearing on "Each test is a constraint"
- **68.10s** (seg 006 ends): All labels visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Mold with dimmed nozzle/cavity, bright walls */}
    <ScaleTransition from={1.0} to={1.15} duration={30}>
      <MoldCrossSection
        wallsOpacity={1.0}
        nozzleOpacity={0.05}
        cavityOpacity={0.05}
        wallColor="#4A90D9"
      />
    </ScaleTransition>

    {/* Wall segment 1 + label */}
    <Sequence from={30}>
      <WallSegment index={0} glowFrom={0.2} glowTo={0.5} duration={15} />
      <Sequence from={5}>
        <FadeIn duration={20}>
          <WallLabel text="null → None" side="left"
            font="JetBrains Mono" size={14}
            color="#CDD6F4" pillColor="#4A90D9" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Wall segment 2 + label */}
    <Sequence from={75}>
      <WallSegment index={1} glowFrom={0.2} glowTo={0.5} duration={15} />
      <Sequence from={5}>
        <FadeIn duration={20}>
          <WallLabel text="empty string → ''" side="right"
            font="JetBrains Mono" size={14}
            color="#CDD6F4" pillColor="#4A90D9" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Wall segment 3 + label */}
    <Sequence from={120}>
      <WallSegment index={2} glowFrom={0.2} glowTo={0.5} duration={15} />
      <Sequence from={5}>
        <FadeIn duration={20}>
          <WallLabel text="handles unicode" side="left"
            font="JetBrains Mono" size={14}
            color="#CDD6F4" pillColor="#4A90D9" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Wall segment 4 + label */}
    <Sequence from={165}>
      <WallSegment index={3} glowFrom={0.2} glowTo={0.5} duration={15} />
      <Sequence from={5}>
        <FadeIn duration={20}>
          <WallLabel text="latency < 100ms" side="right"
            font="JetBrains Mono" size={14}
            color="#CDD6F4" pillColor="#4A90D9" />
        </FadeIn>
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "mold_wall_labels",
  "walls": [
    { "label": "null → None", "side": "left", "frameIn": 30 },
    { "label": "empty string → ''", "side": "right", "frameIn": 75 },
    { "label": "handles unicode", "side": "left", "frameIn": 120 },
    { "label": "latency < 100ms", "side": "right", "frameIn": 165 }
  ],
  "narrationSegments": ["part3_mold_parts_006"],
  "durationSeconds": 10.0
}
```

---
