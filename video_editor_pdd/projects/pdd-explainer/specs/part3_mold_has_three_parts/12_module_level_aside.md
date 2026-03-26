[Remotion]

# Section 3.12: Module-Level Aside — Honest Limitation

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 2:44 - 2:56

## Visual Description

A brief aside acknowledging PDD's scope. A system architecture diagram appears — multiple modules (rounded rectangles) connected by arrows showing data flow and dependencies. One module in the center glows with the characteristic teal/amber mold aura — this is the PDD-governed module.

The glow covers the module interior precisely but stops at its boundaries. The arrows connecting to other modules — the inter-module relationships — are outside the glow, rendered in a neutral gray. This visually communicates that PDD operates at the module level, not the system level.

Label below: "PDD operates at the module level." Sub-label: "Emergent behavior across modules still requires human judgment."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### System Diagram
- 7 module boxes arranged in a network pattern
- Each module: 160×80px, rounded 6px, bg `#1E293B`, border `#334155` at 0.3
- Module labels: Inter, 11px, `#94A3B8` at 0.5 (e.g., "auth", "api", "user_parser", "billing", "cache", "queue", "mailer")
- Connection arrows: 1px, `#334155` at 0.2, with small arrowheads

#### Highlighted Module ("user_parser")
- Same size, but border `#2DD4BF` at 0.5 and `#D9944A` at 0.5 (dual glow)
- Interior fill: gradient `#2DD4BF` at 0.08 to `#D9944A` at 0.05
- Glow aura: 15px radius, combined teal-amber at 0.1
- Label: "user_parser" — Inter, 11px, bold, `#E2E8F0` at 0.8

#### Connection Emphasis
- Arrows TO/FROM highlighted module: `#64748B` at 0.3 — visible but clearly outside the glow
- Small "?" icons at each connection point: `#64748B` at 0.3, 12px

#### Labels
- "PDD operates at the module level." — Inter, 18px, bold, `#E2E8F0` at 0.7, centered at y: 850
- "The mold makes each part precise. The assembly is still yours." — Inter, 14px, `#94A3B8` at 0.5, y: 890

### Animation Sequence
1. **Frame 0-60 (0-2s):** System diagram fades in — all modules neutral.
2. **Frame 60-150 (2-5s):** Central module ("user_parser") begins glowing. Teal-amber aura blooms.
3. **Frame 150-240 (5-8s):** Connection arrows to other modules become visible. "?" icons appear at boundaries.
4. **Frame 240-300 (8-10s):** Labels appear below.
5. **Frame 300-360 (10-12s):** Hold. Module glows, connections neutral. The scope is clear.

### Typography
- Module labels: Inter, 11px, `#94A3B8` at 0.5
- Highlighted module: Inter, 11px, bold, `#E2E8F0` at 0.8
- Main label: Inter, 18px, bold (700), `#E2E8F0` at 0.7
- Sub-label: Inter, 14px, `#94A3B8` at 0.5

### Easing
- Diagram fade-in: `easeOut(quad)` over 30 frames
- Module glow bloom: `easeOut(cubic)` over 40 frames
- "?" appear: `easeOut(quad)` over 15 frames
- Label fade-in: `easeOut(quad)` over 20 frames
- Glow pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "One honest limitation: PDD works at the module level. Each prompt governs one module. Emergent behavior across modules — race conditions, cascading failures, architectural mismatches — still requires human judgment. The mold makes each part precise. The assembly is still yours."

Segment: `part3_mold_has_three_parts_017`

- **2:44** ("One honest limitation"): System diagram appears
- **2:48** ("module level"): Central module begins glowing
- **2:53** ("assembly is still yours"): Labels appear, boundaries emphasized

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* System diagram */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <SystemDiagram modules={MODULES} connections={CONNECTIONS}
          moduleSize={{ width: 160, height: 80 }}
          bg="#1E293B" border="#334155" />
      </FadeIn>
    </Sequence>

    {/* Highlight central module */}
    <Sequence from={60}>
      <GlowBloom duration={40}>
        <ModuleHighlight
          moduleId="user_parser"
          glowColors={["#2DD4BF", "#D9944A"]}
          glowRadius={15} glowOpacity={0.1} />
      </GlowBloom>
    </Sequence>

    {/* Connection boundary markers */}
    <Sequence from={150}>
      {CONNECTIONS_TO_PARSER.map((conn) => (
        <FadeIn duration={15} key={conn.id}>
          <BoundaryMarker x={conn.x} y={conn.y}
            icon="?" color="#64748B" opacity={0.3} size={12} />
        </FadeIn>
      ))}
    </Sequence>

    {/* Labels */}
    <Sequence from={240}>
      <FadeIn duration={20}>
        <Text text="PDD operates at the module level."
          font="Inter" size={18} weight={700} color="#E2E8F0" opacity={0.7}
          x={960} y={850} align="center" />
        <Text text="The mold makes each part precise. The assembly is still yours."
          font="Inter" size={14} color="#94A3B8" opacity={0.5}
          x={960} y={890} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "module_level_aside",
  "modules": ["auth", "api", "user_parser", "billing", "cache", "queue", "mailer"],
  "highlightedModule": "user_parser",
  "highlightColors": ["#2DD4BF", "#D9944A"],
  "limitation": "PDD operates at the module level",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_017"]
}
```

---
