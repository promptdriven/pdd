[Remotion]

# Section 3.11: Module Boundary — Honest Limitation

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 3:28 - 3:51

## Visual Description

A system architecture diagram showing a single module glowing inside a larger system. The module is a rounded rectangle in the center, pulsing with a soft blue glow — this is the PDD-governed unit. Around it, other modules are connected via arrows representing dependencies, API calls, and data flows. These connecting arrows and surrounding modules are outside the glow — they're in muted gray, representing the parts PDD doesn't control.

A label appears: "PDD operates at the module level."

The visual honestly communicates the boundary: PDD makes each part precise, but the connections between parts (race conditions, cascading failures, architectural mismatches) are still the developer's responsibility. The assembly diagram emphasizes that PDD is a component-level tool, not a system-level guarantee.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Central Module (PDD-governed)
- Rounded rectangle: 240px × 120px, `#1E1E2E` fill, `#4A90D9` border 2px, rounded 12px
- Label: "user_parser" — JetBrains Mono, 14px, bold (700), `#CDD6F4`
- Glow: `#4A90D9` at 0.25, 20px blur, pulsing
- Position: centered at (960, 540)

#### Surrounding Modules (non-PDD)
- 6 modules arranged radially around center
- Same shape: 180px × 80px, `#1E1E2E` fill, `#334155` border 1px (muted), rounded 8px
- Labels: "auth_service", "db_layer", "api_router", "cache", "logger", "config" — JetBrains Mono, 12px, `#64748B`
- No glow — explicitly outside PDD's scope

#### Connection Arrows
- Bidirectional arrows between central module and surrounding modules
- Arrow color: `#334155` at 0.5, 1.5px
- Arrowheads: small triangles
- Dashed where connections represent async/event-driven

#### Boundary Visualization
- Dotted circle around central module: `#4A90D9` at 0.15, radius 180px, 2px dashed
- Label on the circle: "PDD boundary" — Inter, 11px, `#4A90D9` at 0.4

#### Main Label
- "PDD operates at the module level." — Inter, 22px, semi-bold (600), `#E2E8F0`
- Position: centered at y: 800
- Subtext: "The mold makes each part precise. The assembly is still yours." — Inter, 14px, regular (400), `#94A3B8`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Central module fades in with glow.
2. **Frame 30-90 (1-3s):** Surrounding modules fade in one by one (10 frames apart).
3. **Frame 90-150 (3-5s):** Connection arrows draw between central and surrounding modules.
4. **Frame 150-210 (5-7s):** Dotted boundary circle appears around central module. "PDD boundary" label fades in.
5. **Frame 210-300 (7-10s):** Surrounding modules dim slightly (opacity 1.0 → 0.6). The central module's glow strengthens. The contrast shows scope.
6. **Frame 300-420 (10-14s):** Main label fades in: "PDD operates at the module level."
7. **Frame 420-540 (14-18s):** Subtext fades in: "The mold makes each part precise. The assembly is still yours."
8. **Frame 540-660 (18-22s):** Hold. Central module pulses gently. Surrounding modules are clear but muted.

### Typography
- Module labels (center): JetBrains Mono, 14px, bold (700), `#CDD6F4`
- Module labels (surround): JetBrains Mono, 12px, regular (400), `#64748B`
- Boundary label: Inter, 11px, regular (400), `#4A90D9` at 0.4
- Main label: Inter, 22px, semi-bold (600), `#E2E8F0`
- Subtext: Inter, 14px, regular (400), `#94A3B8`

### Easing
- Module fade-in: `easeOut(quad)` over 15 frames
- Arrow draw: `easeOut(quad)` over 20 frames
- Boundary circle: `easeInOut(cubic)` stroke-dashoffset over 30 frames
- Dim surrounding: `easeInOut(sine)` over 30 frames
- Label fade-in: `easeOut(quad)` over 20 frames
- Glow pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "One honest limitation: PDD works at the module level. Each prompt governs one module. Emergent behavior across modules — race conditions, cascading failures, architectural mismatches — still requires human judgment. The mold makes each part precise. The assembly is still yours."

Segment: `part3_mold_parts_015`

- **208.40s** (seg 015): Central module appears — "One honest limitation"
- **212.0s**: Surrounding modules appear — "Each prompt governs one module"
- **218.0s**: Connections draw — "Emergent behavior across modules"
- **224.0s**: Boundary visible — "still requires human judgment"
- **228.0s**: Label — "The mold makes each part precise. The assembly is still yours."
- **230.78s** (seg 015 ends): Hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Central PDD module */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <ModuleBox
          label="user_parser" x={960} y={540}
          width={240} height={120}
          borderColor="#4A90D9" glow={{ color: "#4A90D9", blur: 20, opacity: 0.25 }}
          labelFont="JetBrains Mono" labelSize={14} labelWeight={700}
        />
      </FadeIn>
    </Sequence>

    {/* Surrounding modules */}
    {SURROUNDING_MODULES.map((mod, i) => (
      <Sequence key={i} from={30 + i * 10}>
        <FadeIn duration={15}>
          <ModuleBox
            label={mod.name} x={mod.x} y={mod.y}
            width={180} height={80}
            borderColor="#334155"
            labelFont="JetBrains Mono" labelSize={12}
            labelColor="#64748B"
          />
        </FadeIn>
      </Sequence>
    ))}

    {/* Connection arrows */}
    <Sequence from={90}>
      {CONNECTIONS.map((conn, i) => (
        <DrawArrow key={i} from={conn.from} to={conn.to}
          color="#334155" opacity={0.5} width={1.5}
          dashed={conn.async} drawDuration={20} />
      ))}
    </Sequence>

    {/* PDD boundary circle */}
    <Sequence from={150}>
      <StrokeDraw duration={30}>
        <DashedCircle center={[960, 540]} radius={180}
          color="#4A90D9" opacity={0.15} strokeWidth={2} />
      </StrokeDraw>
      <Sequence from={15}>
        <FadeIn duration={15}>
          <Text text="PDD boundary" color="#4A90D9" opacity={0.4}
            font="Inter" size={11} x={960} y={345} />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Dim surrounding */}
    <Sequence from={210}>
      <OpacityTransition targets="surrounding" from={1.0} to={0.6} duration={30} />
    </Sequence>

    {/* Labels */}
    <Sequence from={300}>
      <FadeIn duration={20}>
        <Text text="PDD operates at the module level."
          font="Inter" size={22} weight={600} color="#E2E8F0"
          x={960} y={800} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={420}>
      <FadeIn duration={20}>
        <Text text="The mold makes each part precise. The assembly is still yours."
          font="Inter" size={14} color="#94A3B8"
          x={960} y={840} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "system_diagram",
  "centralModule": { "name": "user_parser", "color": "#4A90D9", "governed": true },
  "surroundingModules": [
    { "name": "auth_service", "governed": false },
    { "name": "db_layer", "governed": false },
    { "name": "api_router", "governed": false },
    { "name": "cache", "governed": false },
    { "name": "logger", "governed": false },
    { "name": "config", "governed": false }
  ],
  "label": "PDD operates at the module level.",
  "narrationSegments": ["part3_mold_parts_015"],
  "durationSeconds": 22.0
}
```

---
