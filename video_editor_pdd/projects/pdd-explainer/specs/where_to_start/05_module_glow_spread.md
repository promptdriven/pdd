[Remotion]

# Section 6.5: Spreading Glow — Gradual Migration

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:20 - 0:26

## Visual Description

The codebase view is now pulled back far enough to see the full system — a grid of 12-15 module rectangles arranged in a loose network layout, connected by thin dependency lines. Two modules (auth_handler, payment_processor) already glow blue, indicating they've been migrated to prompt-driven. The rest are gray.

One by one, additional modules begin to glow. Not simultaneously — sequentially, organically, like a network lighting up. Each module's transformation follows a compressed version of the previous animation: a brief flash, the prompt icon appears, the code dims, and the glow settles. The dependency lines between migrated modules shift from gray to a faint blue, showing the growing "prompt-driven zone."

By the end of the shot, roughly 6-7 of the 12-15 modules are glowing. The migration is not complete — and that's the point. The visual communicates gradual, risk-free, one-module-at-a-time adoption. No big bang.

A small percentage counter in the corner ticks up: "15% → 25% → 40% → 50%" as modules light up.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Module Network Graph
- 14 module nodes arranged in organic cluster layout
- Node size: 90x55px rounded rectangles
- Node background: `#1E293B` at 0.6 (unmigrated), `#111827` at 0.9 with `#60A5FA` glow (migrated)
- Node border: 1px `#334155` at 0.3 (unmigrated), 1px `#60A5FA` at 0.4 (migrated)
- Node labels: JetBrains Mono, 8px, `#94A3B8` at 0.5 (file names, truncated)
- Migrated node glow: 10px blur, `#60A5FA` at 0.1
- Prompt icon (migrated): small 8x10px blue rectangle beside each migrated node, `#60A5FA` at 0.5

#### Dependency Lines
- Connecting lines between related modules
- Unmigrated: 1px, `#334155` at 0.15
- Migrated (both endpoints): 1px, `#60A5FA` at 0.2
- Mixed (one migrated, one not): 1px, `#334155` at 0.1 with dashed pattern

#### Pre-migrated Modules (frame 0)
- `auth_handler.py` at (400, 350) — already glowing
- `payment_processor.py` at (600, 420) — already glowing

#### Modules that migrate during animation
- `user_service.py` at (820, 310) — migrates at frame 20
- `config.py` at (350, 550) — migrates at frame 45
- `db_connector.py` at (650, 580) — migrates at frame 65
- `email_sender.py` at (1050, 400) — migrates at frame 85
- `cache_layer.py` at (900, 550) — migrates at frame 105

#### Remaining Unmigrated
- `legacy_router.py` at (1200, 320)
- `reporting.py` at (1100, 560)
- `webhook_handler.py` at (500, 200)
- `session_manager.py` at (750, 180)
- `rate_limiter.py` at (1000, 220)
- `notification_service.py` at (1250, 480)
- `data_exporter.py` at (850, 680)

#### Migration Counter
- Position: (1740, 100)
- Format: "NN% prompt-driven" — Inter, 16px, bold (700), `#60A5FA` at 0.6
- Ticks: 15% → 22% → 29% → 36% → 43% → 50%
- Backdrop: rounded rect, `#111827` at 0.5, 8px padding

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Full network visible. Auth_handler and payment_processor already glowing. Counter shows "15%".
2. **Frame 20-35 (0.67-1.17s):** `user_service.py` flashes and migrates. Glow appears. Counter ticks to "22%". Dependency line to auth_handler turns blue.
3. **Frame 45-60 (1.5-2s):** `config.py` migrates. Counter: "29%".
4. **Frame 65-80 (2.17-2.67s):** `db_connector.py` migrates. Counter: "36%". Cluster of blue grows.
5. **Frame 85-100 (2.83-3.33s):** `email_sender.py` migrates. Counter: "43%".
6. **Frame 105-120 (3.5-4s):** `cache_layer.py` migrates. Counter: "50%". The blue zone now dominates the left-center.
7. **Frame 120-180 (4-6s):** Hold. Migrated modules pulse gently in unison. Unmigrated modules remain gray and still. The contrast is clear.

### Typography
- Module labels: JetBrains Mono, 8px, `#94A3B8` at 0.5
- Migration counter: Inter, 16px, bold (700), `#60A5FA` at 0.6
- Counter label: Inter, 11px, `#94A3B8` at 0.4

### Easing
- Module migration flash: `easeOut(cubic)` over 10 frames
- Glow appear: `easeOut(quad)` over 10 frames
- Dependency line color shift: `easeInOut(quad)` over 15 frames
- Counter tick: `easeOut(quad)` with number interpolation
- Hold pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "Just a gradual migration of where value lives — from code to specification."

Segment: `where_to_start_002`

- **0:20** ("Just a gradual migration"): Modules begin lighting up one by one
- **0:22** ("where value lives"): Migration counter climbing, blue zone spreading
- **0:25** ("from code to specification"): Hold at 50% — the visual makes it clear this is an ongoing process, not a completed one

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dependency lines (rendered first, below nodes) */}
    <DependencyGraph
      edges={edges}
      migratedNodes={migratedSet}
      unmigColor="#334155"
      migColor="#60A5FA"
      mixedDash={true}
    />

    {/* Module nodes */}
    {modules.map((mod) => (
      <ModuleNode
        key={mod.name}
        name={mod.name}
        x={mod.x} y={mod.y}
        width={90} height={55}
        migrated={mod.migratedAt !== null}
        migrateAtFrame={mod.migratedAt}
        unmigBg="#1E293B"
        migBg="#111827"
        glowColor="#60A5FA"
        glowBlur={10}
        labelFont="JetBrains Mono"
        labelSize={8}
      />
    ))}

    {/* Migration counter */}
    <Sequence from={0}>
      <MigrationCounter
        x={1740} y={100}
        steps={[
          { frame: 0, value: 15 },
          { frame: 35, value: 22 },
          { frame: 60, value: 29 },
          { frame: 80, value: 36 },
          { frame: 100, value: 43 },
          { frame: 120, value: 50 }
        ]}
        suffix="% prompt-driven"
        color="#60A5FA"
        bgColor="#111827"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "network_graph",
  "chartId": "module_glow_spread",
  "totalModules": 14,
  "migrationSequence": [
    { "name": "auth_handler.py", "frame": 0, "position": [400, 350] },
    { "name": "payment_processor.py", "frame": 0, "position": [600, 420] },
    { "name": "user_service.py", "frame": 20, "position": [820, 310] },
    { "name": "config.py", "frame": 45, "position": [350, 550] },
    { "name": "db_connector.py", "frame": 65, "position": [650, 580] },
    { "name": "email_sender.py", "frame": 85, "position": [1050, 400] },
    { "name": "cache_layer.py", "frame": 105, "position": [900, 550] }
  ],
  "unmigrated": [
    "legacy_router.py", "reporting.py", "webhook_handler.py",
    "session_manager.py", "rate_limiter.py", "notification_service.py",
    "data_exporter.py"
  ],
  "counterSteps": [15, 22, 29, 36, 43, 50],
  "colors": {
    "migrated": "#60A5FA",
    "unmigrated": "#1E293B",
    "dependency_migrated": "#60A5FA",
    "dependency_unmigrated": "#334155"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
