[Remotion]

# Section 6.4: Source of Truth Shift

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:15 - 0:20

## Visual Description

The view zooms out slightly from the single highlighted module to show the broader codebase. The `auth_handler.py` module is now clearly split into two visual states: the original code file (gray, muted, labeled "artifact") and the new prompt file beside it (glowing blue, labeled "source of truth"). A thin connecting arrow links them — prompt → code — showing the generation direction.

A second module now begins the same transformation. `payment_processor.py` highlights, a brief terminal flash shows `pdd update payment_processor.py`, and its own prompt file materializes. The code file grays out. The pattern is established — this isn't a one-time trick, it's a repeatable workflow.

A small workflow diagram begins to form in the lower-right: `module → prompt → tests → regenerate → compare`. Each step appears as a node in a horizontal flow, connected by thin arrows. This diagram stays subtle — it's a mental model reinforcement, not the main visual.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Module Pair: auth_handler (already transformed)
- Code panel: `#111827` at 0.3, grayscale(0.8), positioned at (300, 250)
- Prompt icon: `#60A5FA` glow, positioned at (420, 250)
- Arrow: thin, 1px, `#60A5FA` at 0.3, from prompt to code
- Label "artifact": Inter, 9px, `#64748B` at 0.25, below code
- Label "source of truth": Inter, 9px, `#60A5FA` at 0.4, below prompt

#### Module Pair: payment_processor (transforming)
- Code panel: starts at full brightness `#111827` at 0.9, positioned at (300, 480)
- Prompt icon: materializes at (420, 480) with `#60A5FA` glow
- Arrow: draws from prompt to code
- Same label pattern as auth_handler

#### Remaining Modules (background)
- 6-8 dimmed code panels scattered across canvas
- Each: `#111827` at 0.15, code text invisible
- File names barely legible: `#475569` at 0.2

#### Workflow Diagram (lower-right)
- Position: (1200, 920) to (1820, 970)
- 5 nodes in horizontal flow:
  - "module" — rounded rect, `#334155` at 0.4, 10px text
  - "prompt" — rounded rect, `#60A5FA` at 0.3, 10px text
  - "tests" — rounded rect, `#D9944A` at 0.3, 10px text
  - "regenerate" — rounded rect, `#A78BFA` at 0.3, 10px text
  - "compare" — rounded rect, `#4ADE80` at 0.3, 10px text
- Connecting arrows: 1px, `#475569` at 0.3
- All text: Inter, 10px, `#94A3B8` at 0.5

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Camera eases out slightly. Auth_handler pair already in transformed state. Background modules visible but dimmed.
2. **Frame 20-40 (0.67-1.33s):** `payment_processor.py` highlights with selection glow. Brief terminal flash overlay: `pdd update payment_processor.py`.
3. **Frame 40-70 (1.33-2.33s):** Prompt file materializes for payment_processor. Code panel grays out. Arrow draws. Labels appear.
4. **Frame 70-110 (2.33-3.67s):** Workflow diagram nodes appear sequentially, left to right, 8 frames apart. Arrows draw between nodes.
5. **Frame 110-150 (3.67-5s):** Hold. Both transformed pairs pulse gently. Workflow diagram is complete and subtle.

### Typography
- Module labels: Inter, 9px, respective colors
- File names: JetBrains Mono, 10px, `#94A3B8` at 0.5
- Workflow nodes: Inter, 10px, `#94A3B8` at 0.5
- Terminal flash: JetBrains Mono, 11px, `#E2E8F0` at 0.7

### Easing
- Zoom out: `easeInOut(cubic)` over 20 frames
- Module highlight: `easeOut(cubic)` over 15 frames
- Prompt materialize: `easeOut(back)` over 20 frames
- Code desaturate: `easeInOut(quad)` over 20 frames
- Workflow node appear: `easeOut(quad)` over 12 frames each
- Glow pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "One module at a time. No big bang. No rewrite."

Segment: `where_to_start_002`

- **0:15** ("One module at a time"): Second module begins transformation
- **0:17** ("No big bang"): Prompt materializes, code grays
- **0:19** ("No rewrite"): Workflow diagram assembles — the process is incremental

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Auth handler — already transformed */}
    <ModulePair
      name="auth_handler.py"
      codePosition={[300, 250]}
      promptPosition={[420, 250]}
      codeOpacity={0.3}
      codeGrayscale={0.8}
      promptGlow={{ color: "#60A5FA", blur: 16, opacity: 0.12 }}
      arrowColor="#60A5FA"
      labels={true}
    />

    {/* Payment processor — transforming */}
    <Sequence from={20}>
      <ModuleTransform
        name="payment_processor.py"
        codePosition={[300, 480]}
        promptPosition={[420, 480]}
        highlightDuration={15}
        highlightColor="#60A5FA"
        terminalFlash="pdd update payment_processor.py"
        transformDelay={20}
        transformDuration={30}
      />
    </Sequence>

    {/* Background dimmed modules */}
    <DimmedModules
      modules={["user_service.py", "legacy_router.py", "config.py",
                "db_connector.py", "email_sender.py", "cache_layer.py"]}
      opacity={0.15}
    />

    {/* Workflow diagram */}
    <Sequence from={70}>
      <WorkflowDiagram
        x={1200} y={920}
        nodes={[
          { label: "module", color: "#334155" },
          { label: "prompt", color: "#60A5FA" },
          { label: "tests", color: "#D9944A" },
          { label: "regenerate", color: "#A78BFA" },
          { label: "compare", color: "#4ADE80" }
        ]}
        nodeDelay={8}
        arrowColor="#475569"
        textColor="#94A3B8"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_transformation",
  "chartId": "source_of_truth_shift",
  "transformedModules": [
    { "name": "auth_handler.py", "state": "complete" },
    { "name": "payment_processor.py", "state": "animating" }
  ],
  "pendingModules": [
    "user_service.py", "legacy_router.py", "config.py",
    "db_connector.py", "email_sender.py", "cache_layer.py"
  ],
  "workflow": ["module", "prompt", "tests", "regenerate", "compare"],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
