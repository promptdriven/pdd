[Remotion]

# Section 0.4: Zoom Out Accumulated — Codebase Reveal

**Tool:** Remotion
**Duration:** ~5.5s (164 frames @ 30fps)
**Timestamp:** 0:06 - 0:11

## Visual Description

A Remotion-rendered zoom-out animation that replaces the LEFT panel's Veo footage during the split screen's "reveal" phase. What appeared to be a single clean AI-assisted edit is revealed to be one tiny patch in a massive, sprawling codebase.

The animation starts zoomed in on a single file showing the edit that just landed — clean, highlighted in green. Then the camera zooms out rapidly, revealing layer after layer of code: more files, more tabs, more diff markers. TODO comments, `// HACK`, `// temporary fix`, and `// don't touch this` annotations pepper the landscape. File explorer trees expand. The single edit shrinks to a pixel in an ocean of accumulated patches.

The visual metaphor is clear: the edit was excellent. The problem is everything around it.

The aesthetic matches VS Code / Cursor's dark theme — `#0D1117` background, syntax-highlighted code, familiar IDE chrome. The zoom-out uses a 2.5D layered approach where files appear at different depths, creating parallax.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9) — renders into LEFT half of split (958x1080 viewport)
- Background: `#0D1117` (IDE dark background)
- Grid lines: None

### Chart/Visual Elements

#### Initial View (Zoomed In)
- Single file open: `UserService.ts` — JetBrains Mono, 11px, syntax-highlighted
- One line highlighted green `#5AAA6E` at 0.15 background — the AI edit that just landed
- Cursor blinking at end of edited line
- File tab active: `UserService.ts` with green dot (modified)

#### Zoom-Out Layers (Progressive Reveal)
- **Layer 1 (scale 1.0→0.6):** Adjacent files appear — 3-4 file tabs: `AuthController.ts`, `DatabaseHelper.ts`, `legacy_utils.py`
- **Layer 2 (scale 0.6→0.3):** File explorer tree slides in from left — 40+ files visible, deep nesting
- **Layer 3 (scale 0.3→0.15):** Multiple editor groups / split panes — diff markers (`+`, `-`, `~`) scattered across files
- **Layer 4 (scale 0.15→0.10):** Full workspace view — TODO comments float as labels: `// HACK`, `// temporary fix (2019)`, `// don't touch this`, `// TODO: refactor someday`

#### Visual Markers (appear during zoom-out)
- Diff markers: `+` in `#5AAA6E`, `-` in `#E74C3C`, `~` in `#D9944A` — scattered across files
- TODO/HACK labels: Inter, 8px, `#E74C3C` at 0.5, with slight rotation (-2° to +2°)
- Original edit: green highlight shrinks to a tiny dot — barely visible at final zoom level

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Zoomed in on single file. Green-highlighted edit visible. Cursor blinks.
2. **Frame 15-50 (0.5-1.67s):** Zoom begins. Scale 1.0→0.6. Adjacent files and tabs appear. First TODO labels fade in.
3. **Frame 50-90 (1.67-3s):** Scale 0.6→0.3. File explorer tree slides in. Diff markers scatter across the expanding view.
4. **Frame 90-120 (3-4s):** Scale 0.3→0.15. Multiple editor panes. The codebase feels enormous. HACK/legacy labels appear.
5. **Frame 120-140 (4-4.67s):** Scale 0.15→0.10. Final zoom level. The original edit is a tiny green speck. The accumulated weight is overwhelming.
6. **Frame 140-164 (4.67-5.5s):** Hold at final zoom. Gentle drift (~0.5px/frame leftward) to suggest the codebase extends even further.

### Typography
- Code text: JetBrains Mono, 11px (scales down with zoom), syntax colors
- File tabs: Inter, 11px, `#E2E8F0` at 0.7
- TODO/HACK labels: Inter, 8px, `#E74C3C` at 0.5
- File tree: Inter, 10px, `#94A3B8` at 0.4

### Easing
- Zoom-out: `easeInOut(cubic)` — starts slow, accelerates through middle layers, settles at end
- File/tab reveals: `easeOut(quad)` over 15 frames each, staggered
- TODO label fade-in: `easeOut(quad)` over 10 frames, staggered by layer
- Final drift: `linear` — constant slow movement

## Narration Sync
> "Ah, but here's what your grandmother could have told you: the goal was never to get better at darning."

Segment: `cold_open_003`

- **0:06** ("here's what your grandmother"): Zoom-out begins, first additional files appear
- **0:08** ("the goal was never"): Deep zoom — codebase sprawl visible
- **0:10** ("to get better at darning"): Final zoom level — the single edit is lost in accumulated patches

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={164}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    <ZoomContainer
      fromScale={1.0} toScale={0.10}
      easing="easeInOutCubic"
      driftX={-0.5} driftPhaseStart={140}
    >
      {/* Layer 0: The original edit */}
      <CodeFile
        name="UserService.ts"
        language="typescript"
        highlightLine={14}
        highlightColor="#5AAA6E"
        cursorBlink
      />

      {/* Layer 1: Adjacent files (appear at scale ~0.6) */}
      <Sequence from={15}>
        <FadeIn duration={15}>
          <FileTabBar tabs={['AuthController.ts', 'DatabaseHelper.ts', 'legacy_utils.py']}
            activeTab={0} />
          <CodeFile name="AuthController.ts" offset={{ x: 400, y: 0 }} />
        </FadeIn>
      </Sequence>

      {/* Layer 2: File tree (appear at scale ~0.3) */}
      <Sequence from={50}>
        <SlideIn from="left" duration={20}>
          <FileExplorer fileCount={42} depth={6}
            font="Inter" fontSize={10} color="#94A3B8" />
        </SlideIn>
        <DiffMarkers count={25} stagger={3} />
      </Sequence>

      {/* Layer 3: Multiple panes + labels (appear at scale ~0.15) */}
      <Sequence from={90}>
        <FadeIn duration={15}>
          <EditorPanes count={4} layout="grid" />
          <TodoLabels
            labels={['// HACK', '// temporary fix (2019)', '// don\'t touch this', '// TODO: refactor someday']}
            color="#E74C3C" opacity={0.5}
            rotationRange={[-2, 2]}
            stagger={5}
          />
        </FadeIn>
      </Sequence>
    </ZoomContainer>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "animationType": "zoom_out_reveal",
  "initialFile": "UserService.ts",
  "editHighlight": { "line": 14, "color": "#5AAA6E" },
  "zoomLevels": [
    { "scale": 1.0, "frame": 0, "content": "single_file_edit" },
    { "scale": 0.6, "frame": 15, "content": "adjacent_files" },
    { "scale": 0.3, "frame": 50, "content": "file_tree_diffs" },
    { "scale": 0.15, "frame": 90, "content": "multi_pane_labels" },
    { "scale": 0.10, "frame": 120, "content": "full_workspace" }
  ],
  "markers": {
    "diffCount": 25,
    "todoLabels": ["// HACK", "// temporary fix (2019)", "// don't touch this", "// TODO: refactor someday"],
    "totalFiles": 42
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_003"],
  "parentSplit": "01_split_screen_hook",
  "panelPosition": "left"
}
```

---
