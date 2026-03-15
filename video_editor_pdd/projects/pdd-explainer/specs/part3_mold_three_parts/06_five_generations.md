[Remotion]

# Section 3.6: Generate Five — Pick the One That Passes

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 14:11 - 14:27

## Visual Description
Five code generation "film frames" appear side by side, like a filmstrip or contact sheet. Each represents a different generation from the same prompt. They animate in simultaneously, then are tested against the wall constraints. Two get red X marks (failed tests), two get yellow warning triangles (partial passes), and one glows green with a checkmark (all tests pass). The winning generation is selected and scales up slightly while the others dim. A brief Z3/SMT sidebar annotation appears, connecting PDD's formal verification to chip industry practices.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Film Frames:** 5 rectangular panels arranged horizontally, each 280px wide x 400px tall, 40px gap between them, centered vertically at Y=250
  - Frame border: 2px `rgba(255,255,255,0.2)`, rounded corners 8px
  - Interior: Faint code-line texture (horizontal lines, `rgba(255,255,255,0.04)`) — each panel has slightly different line patterns to suggest different implementations
  - Frame numbers: "Gen 1" through "Gen 5" — `#94A3B8`, 12px, top-left of each frame
- **Test Result Icons (centered below each frame at Y=680):**
  - Gen 1: Red X — `#EF4444`, 32px, with faint red glow
  - Gen 2: Yellow warning triangle — `#F59E0B`, 28px
  - Gen 3: Red X — `#EF4444`, 32px
  - Gen 4: Yellow warning triangle — `#F59E0B`, 28px
  - Gen 5: Green checkmark — `#22C55E`, 36px, with green glow `rgba(34,197,94,0.3)` blur 8px
- **Winner Highlight:** Gen 5 frame gets a 3px border in `#22C55E` and scales to 1.05×. Other frames dim to 0.3 opacity
- **Selection Label:** "All tests pass" — `#22C55E`, 20px bold, centered below Gen 5 at Y=730
- **Z3 Sidebar (bottom-left, compact):**
  - Small annotation box, 400px wide x 80px tall, `rgba(0,0,0,0.3)` background, rounded 6px
  - Text: "PDD also uses Z3 — the same class of SMT solver used in chip verification — to formally prove properties hold for every possible input." — `#94A3B8`, 13px
  - Small icons: Z3 logo silhouette + Synopsys Formality silhouette, side by side, `rgba(255,255,255,0.3)`

### Animation Sequence
1. **Frame 0-60 (0-2.0s):** Five film frames slide up from below (translateY 40→0) with 8-frame stagger, opacity 0→1. Code textures visible inside
2. **Frame 60-120 (2.0-4.0s):** Test execution animation — a horizontal "scan line" sweeps across all five frames simultaneously (left-to-right, `rgba(255,255,255,0.1)`, 2px), suggesting testing
3. **Frame 120-180 (4.0-6.0s):** Results appear with 10-frame stagger:
   - Gen 1: Red X drops in (scale 0→1.1→1.0)
   - Gen 2: Yellow triangle fades in
   - Gen 3: Red X drops in
   - Gen 4: Yellow triangle fades in
   - Gen 5: Green checkmark bounces in (scale 0→1.3→1.0) with glow
4. **Frame 180-240 (6.0-8.0s):** Winner selection — Gen 5 scales up to 1.05× with green border. Other four frames dim (opacity 1→0.3). "All tests pass" label fades in
5. **Frame 240-300 (8.0-10.0s):** Text appears centered: "The walls don't care how many attempts it took." — `#FFFFFF`, 22px, Y=800
6. **Frame 300-420 (10.0-14.0s):** Z3 sidebar annotation slides in from left. Text and icons fade in. Brief: connecting to chip industry formal verification
7. **Frame 420-480 (14.0-16.0s):** Hold at final state

### Typography
- Frame Labels: JetBrains Mono, 12px, regular (400), `#94A3B8`
- Result Icons: Custom SVG paths
- "All tests pass": Inter, 20px, bold (700), `#22C55E`
- Emphasis Text: Inter, 22px, semi-bold (600), `#FFFFFF`
- Z3 Sidebar: Inter, 13px, regular (400), `#94A3B8`

### Easing
- Frame slide-up: `easeOut(cubic)`
- Scan line sweep: `linear`
- Red X drop: `easeOut(back(1.3))`
- Green checkmark bounce: `easeOut(back(2.0))`
- Winner scale: `easeOut(quad)`
- Dim others: `easeOut(quad)`
- Z3 sidebar slide: `easeOut(cubic)`

## Narration Sync
> "Now — you might be thinking: 'But LLMs don't follow instructions reliably.' You're right. Today. But PDD doesn't need perfection on every run. Generate five versions. Pick the one that passes all tests. The walls don't care how many attempts it took."
> "And some of those walls aren't just tested — they're proven. PDD uses Z3, the same class of SMT solver that the chip industry uses for formal equivalence checking, to mathematically prove that properties hold for every possible input."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  {/* Film Frames */}
  <Sequence from={0} durationInFrames={60}>
    <FilmStrip
      count={5}
      frameWidth={280}
      frameHeight={400}
      gap={40}
      stagger={8}
    />
  </Sequence>

  {/* Test Scan */}
  <Sequence from={60} durationInFrames={60}>
    <ScanLine direction="left-to-right" />
  </Sequence>

  {/* Results */}
  <Sequence from={120} durationInFrames={60}>
    <TestResults
      results={["fail", "warn", "fail", "warn", "pass"]}
      stagger={10}
    />
  </Sequence>

  {/* Winner Selection */}
  <Sequence from={180} durationInFrames={60}>
    <WinnerHighlight index={4} scale={1.05} borderColor="#22C55E" />
    <Label text="All tests pass" color="#22C55E" y={730} />
  </Sequence>

  {/* Emphasis Text */}
  <Sequence from={240} durationInFrames={60}>
    <EmphasisText text="The walls don't care how many attempts it took." y={800} />
  </Sequence>

  {/* Z3 Sidebar */}
  <Sequence from={300} durationInFrames={120}>
    <Z3Sidebar />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "filmStrip": {
    "count": 5,
    "frameWidth": 280,
    "frameHeight": 400,
    "gap": 40,
    "borderColor": "rgba(255,255,255,0.2)"
  },
  "results": [
    { "gen": 1, "result": "fail", "icon": "x", "color": "#EF4444" },
    { "gen": 2, "result": "warn", "icon": "triangle", "color": "#F59E0B" },
    { "gen": 3, "result": "fail", "icon": "x", "color": "#EF4444" },
    { "gen": 4, "result": "warn", "icon": "triangle", "color": "#F59E0B" },
    { "gen": 5, "result": "pass", "icon": "checkmark", "color": "#22C55E" }
  ],
  "winner": {
    "index": 4,
    "scale": 1.05,
    "borderColor": "#22C55E",
    "glowColor": "rgba(34,197,94,0.3)"
  },
  "z3Sidebar": {
    "text": "PDD also uses Z3 — the same class of SMT solver used in chip verification — to formally prove properties hold for every possible input.",
    "backgroundColor": "rgba(0,0,0,0.3)"
  }
}
```

---
