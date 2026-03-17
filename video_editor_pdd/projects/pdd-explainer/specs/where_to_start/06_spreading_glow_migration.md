[Remotion]

# Section 6.6: Spreading Glow Migration — Modules Converting One by One

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:44 - 23:52

## Visual Description

The dense brownfield codebase from shot 02 returns, but now the first module (`auth_handler`) already glows blue — migrated. The remaining ~35 modules sit in their neutral gray state. One by one, additional modules highlight, transform, and begin glowing — each one converting from code-as-source-of-truth to prompt-as-source-of-truth.

The spread is organic, not mechanical. Modules adjacent to already-converted ones convert next, like a wave of blue light propagating through the topology. Each conversion involves a brief flash (the update moment), then a sustained glow. The dependency lines between converted modules brighten to blue; lines between converted and unconverted modules remain gray.

By the end of the animation, approximately 8-10 of the ~40 modules glow blue. The rest remain gray. The codebase is partially converted — this is not a big bang. A counter in the corner tracks: "3 / 40 modules" → "5 / 40" → "8 / 40". The message is clear: gradual, safe, incremental adoption.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Codebase Topology (full, from 02)
- 40 rectangular blocks in 5-6 cluster groups
- Spread across 1600×800px, centered
- ~60 dependency edges

#### Module States
- **Unconverted (default):** fill `#1E293B`, border `#334155` at 0.2, 1px
- **Converting (flash):** fill `#1E293B`, border `#4A90D9` at 0.6, 2px, outer glow `#4A90D9` at 0.2, 20px blur — holds for 8 frames
- **Converted (sustained):** fill `#0F172A`, border `#4A90D9` at 0.3, 1.5px, ambient glow `#4A90D9` at 0.08, 12px blur

#### Dependency Edge States
- **Between unconverted:** `#334155` at 0.1, 1px
- **Between converted:** `#4A90D9` at 0.2, 1.5px
- **Mixed (converted ↔ unconverted):** `#334155` at 0.1, 1px (unchanged)

#### Module Counter (top-right corner)
- Position: (1680, 80)
- Format: "N / 40 modules" — Inter, 14px, `#E2E8F0` at 0.5
- Number N in `#4A90D9` at 0.7, bold
- Updates with each conversion

#### Conversion Order
- Wave 1 (frame 0): `auth_handler` already converted (carried over)
- Wave 2 (frame 40): `session_manager`, `token_validator` (adjacent to auth)
- Wave 3 (frame 90): `user_parser`, `role_checker` (next ring)
- Wave 4 (frame 140): `api_router`, `middleware_chain`, `rate_limiter` (spreading further)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Full codebase visible. `auth_handler` already glowing blue. Counter: "1 / 40 modules".
2. **Frame 20-60 (0.67-2s):** Wave 2: `session_manager` and `token_validator` flash and convert. Dependency edges between them and auth brighten. Counter: "3 / 40".
3. **Frame 60-110 (2-3.67s):** Wave 3: `user_parser` and `role_checker` flash and convert. More blue edges form. Counter: "5 / 40".
4. **Frame 110-170 (3.67-5.67s):** Wave 4: `api_router`, `middleware_chain`, `rate_limiter` flash and convert. The blue cluster is now clearly visible — a growing island of specification-driven modules in a sea of gray. Counter: "8 / 40".
5. **Frame 170-240 (5.67-8s):** Hold. The blue cluster pulses gently. The unconverted modules remain gray. The boundary between converted and unconverted is clearly visible. Counter holds at "8 / 40".

### Typography
- Counter: Inter, 14px, `#E2E8F0` at 0.5, number in `#4A90D9` bold
- Module labels (on hover/detail): JetBrains Mono, 8px, `#E2E8F0` at 0.3 — visible only on converting modules during flash

### Easing
- Flash on: `easeOut(cubic)` opacity 0 → 0.6 over 6 frames
- Flash hold: 8 frames at peak
- Flash settle: `easeOut(quad)` opacity 0.6 → 0.3 over 10 frames
- Edge brighten: `easeOut(quad)` over 15 frames
- Counter update: `easeOut(quad)` crossfade over 8 frames
- Cluster pulse: `easeInOut(sine)` on 50-frame cycle, opacity ±0.02

## Narration Sync
> "More modules highlight, one by one. Each generates a prompt. The glow spreads across the codebase. Not all at once — gradually, organically."

Segment: `where_to_start_003`

- **23:44** ("More modules highlight"): Wave 2 begins, first adjacent modules converting
- **23:46** ("one by one"): Conversions staggered, not simultaneous
- **23:48** ("Each generates a prompt"): Wave 3, blue cluster growing
- **23:50** ("The glow spreads across the codebase"): Wave 4, island of blue clearly visible
- **23:52** ("Not all at once — gradually, organically"): Hold on partial conversion, 8/40

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Codebase topology — all blocks */}
    <CodebaseTopology
      blocks={allBlocks} edges={allEdges}
      defaultBlockFill="#1E293B" defaultBorderColor="#334155"
      defaultEdgeColor="#334155" defaultEdgeOpacity={0.1}>

      {/* Pre-converted: auth_handler */}
      <ConvertedModule index={12}
        fill="#0F172A" border={{ color: '#4A90D9', opacity: 0.3 }}
        glow={{ color: '#4A90D9', opacity: 0.08, blur: 12 }} />

      {/* Wave 2 */}
      <Sequence from={20}>
        <ModuleConversion indices={[11, 13]}
          flashDuration={8} flashOpacity={0.6}
          settleDuration={10} settleOpacity={0.3}
          stagger={12} />
      </Sequence>

      {/* Wave 3 */}
      <Sequence from={60}>
        <ModuleConversion indices={[8, 14]}
          flashDuration={8} flashOpacity={0.6}
          settleDuration={10} settleOpacity={0.3}
          stagger={15} />
      </Sequence>

      {/* Wave 4 */}
      <Sequence from={110}>
        <ModuleConversion indices={[6, 9, 15]}
          flashDuration={8} flashOpacity={0.6}
          settleDuration={10} settleOpacity={0.3}
          stagger={12} />
      </Sequence>

      {/* Edge state transitions */}
      <EdgeBrighten
        convertedIndices={convertedAtFrame}
        activeColor="#4A90D9" activeOpacity={0.2}
        transitionDuration={15} />
    </CodebaseTopology>

    {/* Cluster pulse on hold */}
    <Sequence from={170}>
      <PulseGlow indices={allConvertedIndices}
        color="#4A90D9" baseOpacity={0.08}
        amplitude={0.02} period={50} />
    </Sequence>

    {/* Module counter */}
    <AnimatedCounter position={[1680, 80]}
      total={40} color="#4A90D9"
      keyframes={[
        { frame: 0, value: 1 },
        { frame: 40, value: 3 },
        { frame: 90, value: 5 },
        { frame: 140, value: 8 }
      ]}
      font="Inter" fontSize={14}
      labelColor="#E2E8F0" labelOpacity={0.5}
      numberWeight={700} numberOpacity={0.7} />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "migration_animation",
  "totalModules": 40,
  "conversionWaves": [
    { "frame": 0, "modules": ["auth_handler"], "cumulative": 1 },
    { "frame": 20, "modules": ["session_manager", "token_validator"], "cumulative": 3 },
    { "frame": 60, "modules": ["user_parser", "role_checker"], "cumulative": 5 },
    { "frame": 110, "modules": ["api_router", "middleware_chain", "rate_limiter"], "cumulative": 8 }
  ],
  "moduleStates": {
    "unconverted": { "fill": "#1E293B", "border": "#334155" },
    "converting": { "border": "#4A90D9", "glowOpacity": 0.2 },
    "converted": { "fill": "#0F172A", "border": "#4A90D9", "glowOpacity": 0.08 }
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_003"]
}
```

---
