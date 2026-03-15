[Remotion]

# Section 6.3: Pick a Leaf Node — Dependency Tree Visualization

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 22:36 - 22:50

## Visual Description
An animated dependency tree diagram that makes the "self-contained" criterion viscerally clear. A simplified project tree materializes — a root node at the top branches into 5-6 intermediate modules, which branch further into leaf nodes. The tree is initially dim gray. Then the visual highlights the leaf nodes (modules with no downstream dependents) in blue — these pulse and lift slightly. One leaf node gets selected with a glowing ring, and a tooltip appears: "This one. No dependents. Safe to regenerate." The interior nodes briefly flash red to show why they're risky — arrows pointing to their dependents animate, showing the blast radius. The message is clear: start at the edges, not the core.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Tree Structure (centered, Y=100 to Y=750):**
  - Root node: "app" — circle 40px diameter, `rgba(255,255,255,0.15)`, centered at X=960, Y=120
  - Level 1 (Y=280): 4 intermediate nodes — "api", "auth", "models", "utils" — circles 32px, `rgba(255,255,255,0.12)`, evenly distributed at X=360, X=640, X=1280, X=1560
  - Level 2 (Y=440): 6 nodes branching from Level 1
    - From "api": "routes" (X=280), "middleware" (X=440)
    - From "auth": "session" (X=640)
    - From "models": "user" (X=1200), "billing" (X=1360)
    - From "utils": "parser" (X=1560)
  - Level 3 — Leaf nodes (Y=600): 4 leaf nodes
    - "csv_parser" (X=240) — from "routes"
    - "date_fmt" (X=520) — from "middleware"
    - "hash_util" (X=1280) — from "billing"
    - "slug_gen" (X=1560) — from "utils/parser"
  - Connecting lines: 1px, `rgba(255,255,255,0.08)`, straight lines between parent-child
- **Leaf Highlight State:**
  - Leaf nodes change from gray to `#4A90D9` at 0.7 opacity
  - 4px upward drift when highlighted
  - Gently pulse (opacity 0.6→0.8)
- **Selected Leaf ("csv_parser"):**
  - Glowing ring: `#4A90D9`, 48px diameter, 2px stroke, animated pulse
  - Tooltip: Rounded rect 320px x 44px, `rgba(74,144,217,0.12)` fill, border `#4A90D9` at 0.3, positioned above at Y=540
  - Tooltip text: "No dependents. Safe to regenerate." — Inter 14px, `#4A90D9`
- **Danger Flash (interior nodes):**
  - "auth" and "models" flash `#EF4444` at 0.4 opacity briefly
  - Red arrows fan out from these nodes to their children, showing blast radius
  - Label near "auth": "3 modules depend on this" — Inter 12px, `#EF4444` at 0.5
- **Bottom Label:** "Start at the leaves." — Inter 24px bold, `#4A90D9`, centered at Y=860

### Animation Sequence
1. **Frame 0-60 (0-2.0s):** Tree draws in top-down — root appears, then Level 1 (10-frame stagger per node), then Level 2 (10-frame stagger), then Level 3. Connecting lines draw as each child appears
2. **Frame 60-120 (2.0-4.0s):** All nodes settle at gray. Brief pause to let the viewer read the structure
3. **Frame 120-180 (4.0-6.0s):** Leaf nodes highlight — transition from gray to blue. Each lifts 4px upward. Non-leaf nodes dim slightly (opacity drops to 0.08)
4. **Frame 180-240 (6.0-8.0s):** "csv_parser" gets selected — glowing ring scales in (0→1 with back easing). Tooltip fades in above
5. **Frame 240-310 (8.0-10.33s):** Interior danger flash — "auth" and "models" flash red briefly. Red arrows animate outward from them to children. Dependency count labels appear. Flash fades after 40 frames
6. **Frame 310-370 (10.33-12.33s):** Red flash clears. All non-leaf nodes return to dim gray. "Start at the leaves." text fades in at bottom
7. **Frame 370-420 (12.33-14.0s):** Hold at final state. Selected leaf pulses gently. Bottom text steady

### Typography
- Node Labels: JetBrains Mono, 12px, medium (500), `rgba(255,255,255,0.6)` (or respective highlight color)
- Tooltip: Inter, 14px, regular (400), `#4A90D9`
- Dependency Count: Inter, 12px, regular (400), `#EF4444` at 0.5
- Bottom Label: Inter, 24px, bold (700), `#4A90D9`

### Easing
- Tree node appear: `easeOut(quad)`
- Connecting line draw: `linear`
- Leaf highlight: `easeOut(cubic)`
- Leaf lift: `easeOut(quad)`
- Selection ring: `easeOut(back(1.5))`
- Tooltip fade: `easeOut(quad)`
- Red flash: `easeInOut(sine)`
- Red arrows: `easeOut(cubic)`
- Bottom text: `easeOut(quad)`

## Narration Sync
> "Look at your dependency tree. Find the leaf nodes — the modules nothing else depends on. Those are your safe starting points. If you regenerate a leaf, the blast radius is zero. If you start with a core module — your auth layer, your data models — you're risking everything that depends on it."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Tree Draw */}
  <Sequence from={0} durationInFrames={60}>
    <DependencyTree
      nodes={treeData}
      edgeColor="rgba(255,255,255,0.08)"
      nodeColor="rgba(255,255,255,0.12)"
      stagger={10}
    />
  </Sequence>

  {/* Leaf Highlight */}
  <Sequence from={120} durationInFrames={60}>
    <HighlightLeaves
      leafIds={["csv_parser", "date_fmt", "hash_util", "slug_gen"]}
      color="#4A90D9"
      lift={4}
    />
  </Sequence>

  {/* Selection */}
  <Sequence from={180} durationInFrames={60}>
    <SelectionRing nodeId="csv_parser" color="#4A90D9" size={48} />
    <Tooltip
      text="No dependents. Safe to regenerate."
      anchorNode="csv_parser"
      offsetY={-60}
    />
  </Sequence>

  {/* Danger Flash */}
  <Sequence from={240} durationInFrames={70}>
    <DangerFlash
      nodeIds={["auth", "models"]}
      color="#EF4444"
      showDependencyArrows={true}
    />
  </Sequence>

  {/* Bottom Label */}
  <Sequence from={310} durationInFrames={60}>
    <FadeText text="Start at the leaves." fontSize={24} color="#4A90D9" y={860} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "tree": {
    "root": { "id": "app", "x": 960, "y": 120 },
    "levels": [
      {
        "y": 280,
        "nodes": [
          { "id": "api", "label": "api", "x": 360, "parent": "app" },
          { "id": "auth", "label": "auth", "x": 640, "parent": "app" },
          { "id": "models", "label": "models", "x": 1280, "parent": "app" },
          { "id": "utils", "label": "utils", "x": 1560, "parent": "app" }
        ]
      },
      {
        "y": 440,
        "nodes": [
          { "id": "routes", "label": "routes", "x": 280, "parent": "api" },
          { "id": "middleware", "label": "middleware", "x": 440, "parent": "api" },
          { "id": "session", "label": "session", "x": 640, "parent": "auth" },
          { "id": "user", "label": "user", "x": 1200, "parent": "models" },
          { "id": "billing", "label": "billing", "x": 1360, "parent": "models" },
          { "id": "parser", "label": "parser", "x": 1560, "parent": "utils" }
        ]
      },
      {
        "y": 600,
        "nodes": [
          { "id": "csv_parser", "label": "csv_parser", "x": 240, "parent": "routes", "leaf": true },
          { "id": "date_fmt", "label": "date_fmt", "x": 520, "parent": "middleware", "leaf": true },
          { "id": "hash_util", "label": "hash_util", "x": 1280, "parent": "billing", "leaf": true },
          { "id": "slug_gen", "label": "slug_gen", "x": 1560, "parent": "parser", "leaf": true }
        ]
      }
    ]
  },
  "selectedLeaf": "csv_parser",
  "dangerNodes": ["auth", "models"]
}
```

---
