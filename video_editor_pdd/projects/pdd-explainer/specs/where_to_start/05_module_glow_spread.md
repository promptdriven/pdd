[Remotion]

# Section 6.5: Module Glow Spread — Gradual Adoption Across the Codebase

**Tool:** Remotion
**Duration:** ~11s (330 frames @ 30fps)
**Timestamp:** 0:15 - 0:26

## Visual Description

The full codebase returns — the same dense layout from Spec 02, but now viewed from a higher abstraction. The code wall transforms into a schematic module map: a grid of ~20 rectangles representing individual modules/files in the project, each labeled with a filename.

One module (`auth_handler.py`) already glows blue-purple — it was converted in the previous spec. Now, a second module highlights: `user_model.py`. A small prompt icon materializes beside it. It glows. Then a third: `payment_processor.py`. Then `api_routes.py`. One by one, modules light up.

The glow spreads organically — not left-to-right or top-to-bottom, but scattered across the grid, the way a real team would adopt PDD: starting with the modules they understand best, the ones with good test coverage, the natural starting points.

By the end, roughly 8 of the 20 modules glow. The rest remain gray. This is intentional — no big bang. The partial glow says: "You don't have to convert everything. Start where it makes sense."

A counter in the corner tracks: "3/20 modules → 5/20 → 8/20 migrated"

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Module Grid
- 5 columns × 4 rows = 20 modules
- Each module: rounded rectangle, 240x90px
- Grid spacing: 30px horizontal, 20px vertical
- Grid centered at (960, 480)
- Default state: `#1E1E2E` fill, `#334155` 1px border, `#8B949E` filename at 0.5
- Converted state: `#1E1E2E` fill, `#8B5CF6` 2px border, `#8B5CF6` glow 10px at 0.1, filename in `#E2E8F0`

#### Module Labels (filenames)
- Inter, 11px, centered in each rectangle
- Default: `#8B949E` at 0.5
- Converted: `#E2E8F0` at 0.9

#### Module Names (order of conversion)
| Order | Module | Grid Position (col, row) |
|-------|--------|------------------------|
| 1 (pre-converted) | auth_handler.py | (2, 1) |
| 2 | user_model.py | (4, 0) |
| 3 | payment_processor.py | (1, 2) |
| 4 | api_routes.py | (3, 3) |
| 5 | email_service.py | (0, 1) |
| 6 | config_loader.py | (4, 3) |
| 7 | search_index.py | (2, 0) |
| 8 | notification_hub.py | (0, 3) |

Remaining 12 modules stay gray: `db_connection.py`, `cache_manager.py`, `logger.py`, `middleware.py`, `rate_limiter.py`, `session_store.py`, `file_upload.py`, `webhook_handler.py`, `scheduler.py`, `analytics.py`, `admin_panel.py`, `test_runner.py`

#### Prompt Icon (per converted module)
- Small document icon: 12x16px, `#8B5CF6` at 0.6
- Appears to the right of the module rectangle after conversion
- Subtle particle trail during materialization

#### Migration Counter
- Position: top-right corner, x: 1680, y: 80
- Format: "N/20 migrated" — Inter, 16px, semi-bold
- Number: `#8B5CF6`, "/20 migrated": `#64748B` at 0.6
- Updates as each module converts

### Animation Sequence
1. **Frame 0-30 (0-1s):** Module grid fades in. `auth_handler.py` already glows (pre-converted). Counter shows "1/20 migrated".
2. **Frame 30-70 (1-2.33s):** `user_model.py` highlights — border transitions from gray to purple, glow blooms. Prompt icon materializes. Counter: "2/20".
3. **Frame 70-110 (2.33-3.67s):** `payment_processor.py` converts. Counter: "3/20".
4. **Frame 110-150 (3.67-5s):** `api_routes.py` converts. Counter: "4/20".
5. **Frame 150-190 (5-6.33s):** `email_service.py` and `config_loader.py` convert in quicker succession. Counter: "5/20" → "6/20".
6. **Frame 190-230 (6.33-7.67s):** `search_index.py` and `notification_hub.py` convert. Counter: "7/20" → "8/20". Pace accelerating — momentum building.
7. **Frame 230-280 (7.67-9.33s):** Hold. 8 modules glowing, 12 gray. The partial adoption is the visual argument. Glowing modules pulse gently in sync.
8. **Frame 280-330 (9.33-11s):** Camera subtly zooms out 5% to show the full grid. The pattern of scattered blue-purple among gray is organic, not forced. Hold.

### Typography
- Module filenames: Inter, 11px, centered
- Migration counter number: Inter, 16px, semi-bold (600), `#8B5CF6`
- Migration counter suffix: Inter, 16px, `#64748B` at 0.6

### Easing
- Grid fade-in: `easeOut(quad)` over 30 frames
- Module conversion (border + glow): `easeOut(cubic)` over 20 frames per module
- Prompt icon materialize: `easeOut(back)` over 15 frames
- Counter update: `easeOut(quad)` number morph over 10 frames
- Modules 5-8 accelerate: 30-frame gap → 20-frame gap between conversions
- Final zoom-out: `easeInOut(quad)` over 30 frames
- Synchronized pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "One module at a time. No big bang. No rewrite. Just a gradual migration of where value lives — from code to specification."

Segment: `where_to_start_002`

- **0:15** (15.46s): Module grid appears — "One module at a time"
- **0:17** (17.00s): Second and third modules converting — "No big bang"
- **0:19** (19.00s): More modules lighting up — "No rewrite"
- **0:22** (22.00s): 8/20 glowing, hold — "a gradual migration of where value lives"
- **0:25** (25.00s): Zoomed-out view — "from code to specification"
- **0:26** (26.24s): Segment ends

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={330}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Module grid */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <ModuleGrid
          cols={5} rows={4}
          cellWidth={240} cellHeight={90}
          spacingX={30} spacingY={20}
          center={[960, 480]}
          modules={allModules}
          defaultBorder="#334155" defaultFill="#1E1E2E"
        />
      </FadeIn>
    </Sequence>

    {/* Progressive module conversions */}
    {conversionSequence.map((conversion, i) => (
      <Sequence key={i} from={conversion.startFrame}>
        <ModuleConvert
          moduleId={conversion.id}
          borderColor="#8B5CF6" glowColor="#8B5CF6"
          glowRadius={10} glowOpacity={0.1}
          convertDuration={20}
          easing="easeOutCubic"
        />
        <Sequence from={10}>
          <PromptIcon
            position={conversion.iconPosition}
            color="#8B5CF6" opacity={0.6}
            size={[12, 16]}
            fadeIn={15} easing="easeOut(back)"
          />
        </Sequence>
      </Sequence>
    ))}

    {/* Migration counter */}
    <Sequence from={0}>
      <MigrationCounter
        x={1680} y={80} total={20}
        schedule={counterSchedule}
        numberColor="#8B5CF6" numberSize={16} numberWeight={600}
        suffixColor="#64748B" suffixOpacity={0.6}
        font="Inter"
      />
    </Sequence>

    {/* Synchronized pulse on converted modules */}
    <Sequence from={230}>
      <PulseGroup
        targets={convertedModuleIds}
        color="#8B5CF6" opacity={0.1}
        cycleFrames={50} easing="easeInOut(sine)"
      />
    </Sequence>

    {/* Final zoom out */}
    <Sequence from={280}>
      <ZoomOut startScale={1.0} endScale={0.95}
        duration={30} easing="easeInOut(quad)" />
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "progressive_migration",
  "grid": { "cols": 5, "rows": 4, "totalModules": 20 },
  "conversionOrder": [
    { "id": "auth_handler", "label": "auth_handler.py", "col": 2, "row": 1, "frame": 0, "preConverted": true },
    { "id": "user_model", "label": "user_model.py", "col": 4, "row": 0, "frame": 30 },
    { "id": "payment_processor", "label": "payment_processor.py", "col": 1, "row": 2, "frame": 70 },
    { "id": "api_routes", "label": "api_routes.py", "col": 3, "row": 3, "frame": 110 },
    { "id": "email_service", "label": "email_service.py", "col": 0, "row": 1, "frame": 150 },
    { "id": "config_loader", "label": "config_loader.py", "col": 4, "row": 3, "frame": 170 },
    { "id": "search_index", "label": "search_index.py", "col": 2, "row": 0, "frame": 190 },
    { "id": "notification_hub", "label": "notification_hub.py", "col": 0, "row": 3, "frame": 210 }
  ],
  "unconverted": [
    "db_connection.py", "cache_manager.py", "logger.py", "middleware.py",
    "rate_limiter.py", "session_store.py", "file_upload.py", "webhook_handler.py",
    "scheduler.py", "analytics.py", "admin_panel.py", "test_runner.py"
  ],
  "counterSteps": [1, 2, 3, 4, 5, 6, 7, 8],
  "narrationSegments": ["where_to_start_002"]
}
```

---
