[Remotion]

# Section 3.5: Bug Found — Add a Wall

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 1:52 - 2:08

## Visual Description

A bug is discovered in the generated code. A red alert pulse radiates from one section of the code inside the mold cavity. The word "BUG" appears in bold red.

Instead of patching the code, a NEW wall materializes in the mold. The wall slides into position from outside, labeled with the bug condition (e.g., `rejects negative IDs`). In the corner, a subtle terminal window shows:
```
$ pdd bug user_parser
Creating failing test...
```

Then the mold regenerates — the liquid drains and refills, now automatically conforming to the new wall. The terminal updates:
```
$ pdd fix user_parser
All tests passing ✓
```

This is the key insight: bugs become permanent walls, not temporary patches.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Bug Discovery
- Red pulse: radial gradient from `#EF4444` at 0.6 center to transparent edge, 40px radius
- Pulse animation: 3 concentric rings expanding outward
- "BUG" text: Inter, 28px, bold (700), `#EF4444`, centered on the bug location
- Bug location: inside the mold cavity, at a gap between walls

#### New Wall Materialization
- Wall slides in from outside the mold (right side)
- Color: `#4A90D9` matching other walls
- Entry animation: translate X from +200px to final position, with slight overshoot
- Label: `rejects negative IDs` — JetBrains Mono, 14px, `#CDD6F4`, pill background `#4A90D9` at 0.15
- Glow pulse on arrival: `#4A90D9` at 0.5, 15px blur

#### Terminal Window (corner)
- Position: bottom-right corner, 380px × 120px
- Background: `#1E1E2E` at 0.9, border `#334155`, border-radius 6px
- Terminal text: JetBrains Mono, 12px, `#A6E3A1`
- Prompt prefix: `$` in `#94A3B8`

#### Regeneration
- Liquid drains (opacity fade from 1.0 to 0.0 over 20 frames, top to bottom)
- Liquid refills from nozzle (same injection animation as 04, faster — 40 frames)
- New liquid conforms to the additional wall

### Animation Sequence
1. **Frame 0-30 (0-1s):** Bug discovery. Red pulse radiates from cavity. "BUG" text fades in.
2. **Frame 30-60 (1-2s):** Hold on bug. Terminal appears in corner: `$ pdd bug user_parser`.
3. **Frame 60-120 (2-4s):** "BUG" text fades out. New wall slides in from right. Terminal shows "Creating failing test...".
4. **Frame 120-150 (4-5s):** Wall arrives in position. Glow pulse. Label `rejects negative IDs` fades in.
5. **Frame 150-180 (5-6s):** Hold. The wall is now part of the mold.
6. **Frame 180-210 (6-7s):** Liquid in cavity drains (fade out top-to-bottom).
7. **Frame 210-300 (7-10s):** New liquid injects from nozzle, fills cavity, conforms to ALL walls including the new one. Terminal: `$ pdd fix user_parser`.
8. **Frame 300-360 (10-12s):** Terminal shows "All tests passing ✓" in green. New liquid shape is slightly different — constrained by the additional wall.
9. **Frame 360-480 (12-16s):** Hold. The mold has one more wall. The code regenerated cleanly. Terminal fades slightly.

### Typography
- "BUG" text: Inter, 28px, bold (700), `#EF4444`
- Wall label: JetBrains Mono, 14px, regular (400), `#CDD6F4`
- Terminal: JetBrains Mono, 12px, regular (400), `#A6E3A1` / `#94A3B8`

### Easing
- Bug pulse: `easeOut(quad)` expanding rings, 15 frames each
- Wall slide-in: `easeOut(back)` over 40 frames (slight overshoot)
- Liquid drain: `easeIn(quad)` over 20 frames
- Liquid refill: custom bezier `cubic-bezier(0.25, 0.1, 0.25, 1)` over 40 frames
- Terminal fade-in: `easeOut(quad)` over 15 frames

## Narration Sync
> "Now watch what happens when you find a bug... ...you don't patch the code. You add a wall. That wall is permanent. That bug can never occur again — not in this generation, not in any future generation."

Segment: `part3_mold_parts_009`

- **111.78s** (seg 009): Bug pulse appears — "Now watch what happens"
- **116.0s**: Wall materializes — "you don't patch the code"
- **119.0s**: "You add a wall"
- **122.0s**: Regeneration — "That wall is permanent"
- **127.62s** (seg 009 ends): "not in any future generation" — hold on new mold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />
    <MoldCrossSection wallsOpacity={0.4} />

    {/* Bug discovery */}
    <Sequence from={0} durationInFrames={90}>
      <BugPulse center={BUG_LOCATION}
        color="#EF4444" radius={40} rings={3} />
      <Sequence from={10}>
        <FadeIn duration={15}>
          <Text text="BUG" font="Inter" size={28}
            weight={700} color="#EF4444"
            x={BUG_LOCATION[0]} y={BUG_LOCATION[1] - 30} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Terminal */}
    <Sequence from={30}>
      <FadeIn duration={15}>
        <TerminalWindow
          x={1450} y={850} width={380} height={120}
          commands={[
            { text: "pdd bug user_parser", delay: 0 },
            { text: "Creating failing test...", delay: 60, color: "#A6E3A1" },
            { text: "pdd fix user_parser", delay: 210 },
            { text: "All tests passing ✓", delay: 300, color: "#A6E3A1" }
          ]}
        />
      </FadeIn>
    </Sequence>

    {/* New wall slides in */}
    <Sequence from={60}>
      <SlideIn from="right" distance={200} duration={40}
        easing="easeOut(back)">
        <WallSegment
          label="rejects negative IDs"
          color="#4A90D9"
          glowOnArrive={{ opacity: 0.5, blur: 15 }}
        />
      </SlideIn>
    </Sequence>

    {/* Liquid drain + refill */}
    <Sequence from={180}>
      <LiquidDrain duration={20} direction="top-to-bottom" />
    </Sequence>
    <Sequence from={210}>
      <LiquidFlow entryPoint="nozzle"
        gradientFrom="#38BDF8" gradientTo="#0D9488"
        flowDuration={40}
        walls={[...EXISTING_WALLS, NEW_WALL]}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "bug_to_wall",
  "bugLabel": "BUG",
  "newWall": { "label": "rejects negative IDs", "color": "#4A90D9" },
  "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"],
  "narrationSegments": ["part3_mold_parts_009"],
  "durationSeconds": 16.0
}
```

---
