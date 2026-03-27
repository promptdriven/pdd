[Remotion]

# Section 6.5: Module Glow Spread — Gradual Migration

**Tool:** Remotion
**Duration:** ~11s (330 frames @ 30fps)
**Timestamp:** 0:18 - 0:29

## Visual Description

The zoomed-out codebase returns to fill the screen — the same dense grid of modules from spec 02, but now one module (`auth_handler.py`) already glows green from the previous transformation.

One by one, additional modules highlight and undergo the same transformation. Each module:
1. Gets a green border glow
2. A tiny prompt file icon appears next to it
3. The module's code representation grays out

The spread is organic — not a wave, not a grid march. It's more like a growing organism: `auth_handler.py` → `user_service.py` (adjacent) → `payment_processor.py` (jump across) → `email_templates.py` → `api_routes.py` → `config_manager.py`. By the end, roughly 40% of the modules glow green while the rest remain gray, showing partial migration.

A small counter in the bottom-right tracks: "3 / 12 modules migrated" → "6 / 12 modules migrated".

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Module grid: centered, 0.25 scale equivalent from spec 02 zoom-out

### Chart/Visual Elements

#### Module Grid
- 4x3 grid of module rectangles (140x90px each, 30px gap)
- Centered at (960, 450)
- Unmigrated modules: `#1E293B` fill, `#334155` 1px border, `#94A3B8` at 0.3 text labels
- Migrated modules: `#5AAA6E` 2px border, `#5AAA6E` glow at 0.15, 10px blur. Internal content grays. Tiny prompt icon (12x16px, `#5AAA6E`) appears top-right corner.

#### Module Labels
- Each module: Inter, 11px, `#94A3B8` at 0.5 (unmigrated) or `#5AAA6E` at 0.7 (migrated)
- Names: `auth_handler`, `user_service`, `payment_proc`, `email_templates`, `api_routes`, `config_mgr`, `db_models`, `test_utils`, `middleware`, `validators`, `cache_layer`, `logging_setup`

#### Migration Counter
- Position: bottom-right at (1700, 950)
- "N / 12 modules migrated" — Inter, 16px, semi-bold (600), `#5AAA6E`
- Number animates up as modules convert

#### Connecting Lines (optional)
- Faint dashed lines between migrated modules, `#5AAA6E` at 0.08, showing the growing network

### Animation Sequence
1. **Frame 0-30 (0-1s):** Zoomed-out codebase visible. `auth_handler` already glowing green. Counter: "1 / 12".
2. **Frame 30-75 (1-2.5s):** `user_service` highlights — border glow, prompt icon appears, content grays. Counter: "2 / 12".
3. **Frame 75-120 (2.5-4s):** `payment_proc` highlights (non-adjacent jump). Counter: "3 / 12".
4. **Frame 120-165 (4-5.5s):** `email_templates` and `api_routes` highlight in quick succession. Counter: "5 / 12".
5. **Frame 165-210 (5.5-7s):** `config_mgr` highlights. Counter: "6 / 12". Connecting lines between migrated modules draw.
6. **Frame 210-270 (7-9s):** Hold. 6 of 12 modules glow green. The organic, partial migration is clear.
7. **Frame 270-330 (9-11s):** Hold continues. Counter pulses subtly. The visual communicates: this is a journey, not a destination.

### Typography
- Module labels: Inter, 11px, respective colors
- Counter: Inter, 16px, semi-bold (600), `#5AAA6E`

### Easing
- Module highlight: `easeOut(quad)` over 20 frames per module
- Prompt icon scale: `easeOut(back)` over 10 frames
- Counter number change: `easeOut(quad)` over 10 frames
- Connecting lines draw: `easeInOut(quad)` over 20 frames
- Stagger between modules: 45 frames (non-uniform)

## Narration Sync
> "One module at a time. No big bang. No rewrite. Just a gradual migration of where value lives — from code to specification."

Segment: `where_to_start_002`

- **18.56s** (seg 002): Second module begins highlighting — "One module at a time"
- **21.00s**: Third module highlights — "No big bang"
- **24.00s**: Multiple modules glowing — "gradual migration"
- **29.88s** (seg 002 ends): 6 of 12 modules migrated, counter visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={330}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Module grid */}
    <ModuleGrid
      rows={3} cols={4}
      cellSize={{ w: 140, h: 90 }}
      gap={30}
      center={[960, 450]}
      modules={[
        { id: "auth_handler", label: "auth_handler" },
        { id: "user_service", label: "user_service" },
        { id: "payment_proc", label: "payment_proc" },
        { id: "email_templates", label: "email_templates" },
        { id: "api_routes", label: "api_routes" },
        { id: "config_mgr", label: "config_mgr" },
        { id: "db_models", label: "db_models" },
        { id: "test_utils", label: "test_utils" },
        { id: "middleware", label: "middleware" },
        { id: "validators", label: "validators" },
        { id: "cache_layer", label: "cache_layer" },
        { id: "logging_setup", label: "logging_setup" },
      ]}
    />

    {/* Module 1: auth_handler (already migrated) */}
    <MigratedModule target="auth_handler" from={0} />

    {/* Module 2: user_service */}
    <Sequence from={30}>
      <MigrateAnimation target="user_service" duration={20} />
    </Sequence>

    {/* Module 3: payment_proc */}
    <Sequence from={75}>
      <MigrateAnimation target="payment_proc" duration={20} />
    </Sequence>

    {/* Modules 4-5: email_templates, api_routes */}
    <Sequence from={120}>
      <MigrateAnimation target="email_templates" duration={20} />
    </Sequence>
    <Sequence from={140}>
      <MigrateAnimation target="api_routes" duration={20} />
    </Sequence>

    {/* Module 6: config_mgr */}
    <Sequence from={165}>
      <MigrateAnimation target="config_mgr" duration={20} />
    </Sequence>

    {/* Connecting lines between migrated modules */}
    <Sequence from={210}>
      <MigrationConnectors
        modules={["auth_handler", "user_service", "payment_proc",
                  "email_templates", "api_routes", "config_mgr"]}
        color="#5AAA6E" opacity={0.08}
        drawDuration={20}
      />
    </Sequence>

    {/* Migration counter */}
    <MigrationCounter
      total={12}
      milestones={[
        { frame: 0, count: 1 },
        { frame: 50, count: 2 },
        { frame: 95, count: 3 },
        { frame: 140, count: 5 },
        { frame: 185, count: 6 },
      ]}
      position={[1700, 950]}
      color="#5AAA6E"
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "module_migration_animation",
  "animationId": "gradual_glow_spread",
  "totalModules": 12,
  "migratedModules": [
    { "id": "auth_handler", "order": 1, "frameStart": 0 },
    { "id": "user_service", "order": 2, "frameStart": 30 },
    { "id": "payment_proc", "order": 3, "frameStart": 75 },
    { "id": "email_templates", "order": 4, "frameStart": 120 },
    { "id": "api_routes", "order": 5, "frameStart": 140 },
    { "id": "config_mgr", "order": 6, "frameStart": 165 }
  ],
  "unmigrated": ["db_models", "test_utils", "middleware", "validators", "cache_layer", "logging_setup"],
  "narrationSegments": ["where_to_start_002"]
}
```

---
