[Remotion]

# Section 6.2: Legacy Codebase Reveal — Dense Intimidating Code Wall

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:00 - 0:06

## Visual Description

A large, existing codebase fills the screen — dense, intimidating, real. The viewer sees a wall of code rendered in a dark IDE theme. Multiple files are visible as stacked panes, giving the impression of a massive project.

Scattered through the code are notorious developer comments that signal danger:
- `// don't touch`
- `// here be dragons`
- `// TODO: refactor this someday`
- `// nobody knows why this works`
- `// legacy — do not modify`

These comments are highlighted in a warning amber, making them pop against the muted gray code. The code slowly scrolls upward, revealing more and more — the codebase is deep. A faint file tree sidebar is visible on the left, showing dozens of files, reinforcing scale.

The mood is deliberately overwhelming: this is every real developer's starting point.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme)

### Chart/Visual Elements

#### Code Wall
- 3 stacked panes (simulating split editor), each ~350px tall
- Code font: JetBrains Mono, 12px, `#ABB2BF` at 0.7
- Syntax colors (muted): keywords `#C678DD` at 0.5, strings `#98C379` at 0.4, functions `#61AFEF` at 0.5
- Line numbers: `#3B4048` at 0.4, left margin 50px
- Pane dividers: `#21262D`, 1px horizontal lines
- Total visible lines: ~80 across all panes

#### Danger Comments (highlighted)
- Color: `#D9944A` (warm amber) at 0.9, bold
- Background highlight: `#D9944A` at 0.08, rounded 4px
- 5 comments distributed across the 3 panes:
  - Pane 1, line 12: `// don't touch`
  - Pane 1, line 28: `// here be dragons`
  - Pane 2, line 8: `// TODO: refactor this someday`
  - Pane 2, line 22: `// nobody knows why this works`
  - Pane 3, line 15: `// legacy — do not modify`

#### File Tree Sidebar
- Width: 220px, left side
- Background: `#161B22`
- File icons and names: `#8B949E` at 0.5, Inter 11px
- ~30 files listed, nested folders
- Active file highlighted: `#1E293B` at 0.6

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Code wall fades in from black. File tree appears on left.
2. **Frame 20-60 (0.67-2s):** Code begins slow upward scroll (0.5px/frame). First danger comments come into view. `// don't touch` glows amber.
3. **Frame 60-100 (2-3.33s):** More code scrolls. `// here be dragons` enters view and glows. Second pane becomes more visible.
4. **Frame 100-140 (3.33-4.67s):** `// TODO: refactor this someday` and `// nobody knows why this works` glow in sequence. The scale becomes apparent.
5. **Frame 140-160 (4.67-5.33s):** Third pane visible. `// legacy — do not modify` glows. Full wall of code is intimidating.
6. **Frame 160-180 (5.33-6s):** Scroll slows. All danger comments pulse gently together. Hold — the codebase is real and daunting.

### Typography
- Code: JetBrains Mono, 12px, `#ABB2BF` at 0.7
- Line numbers: JetBrains Mono, 12px, `#3B4048` at 0.4
- Danger comments: JetBrains Mono, 12px, bold, `#D9944A` at 0.9
- File tree: Inter, 11px, `#8B949E` at 0.5

### Easing
- Code fade-in: `easeOut(quad)` over 20 frames
- Scroll: `linear` at 0.5px/frame, decelerating to 0 in final 20 frames via `easeOut(quad)`
- Comment glow: `easeOut(cubic)` bloom over 10 frames per comment
- Comment pulse (sustained): `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "PDD can create prompts from existing code."

Segment: `where_to_start_001` (opening)

- **0:00** (0.00s): Legacy codebase appears — visual context for "existing code"
- **0:02** (2.00s): Danger comments glowing — emphasizing the legacy nature
- **0:05** (5.00s): Full intimidating codebase visible — setup complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>

    {/* File tree sidebar */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <FileTreeSidebar
          width={220} background="#161B22"
          files={fileTreeData} activeFile="auth_handler.py"
          font="Inter" fontSize={11} color="#8B949E" opacity={0.5}
        />
      </FadeIn>
    </Sequence>

    {/* Code wall — 3 stacked panes */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <ScrollContainer scrollRate={0.5} decelStart={160} decelDuration={20}>
          {codePanes.map((pane, i) => (
            <CodePane
              key={i}
              lines={pane.lines}
              startLine={pane.startLine}
              font="JetBrains Mono" fontSize={12}
              codeColor="#ABB2BF" codeOpacity={0.7}
              lineNumberColor="#3B4048"
              syntaxColors={{
                keyword: '#C678DD', string: '#98C379', function: '#61AFEF'
              }}
            >
              {pane.dangerComments.map((comment, j) => (
                <DangerComment
                  key={j}
                  line={comment.line}
                  text={comment.text}
                  color="#D9944A"
                  highlightBg="#D9944A"
                  highlightOpacity={0.08}
                  glowDelay={comment.glowFrame}
                  glowDuration={10}
                  pulseCycle={60}
                />
              ))}
            </CodePane>
          ))}
        </ScrollContainer>
      </FadeIn>
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_wall",
  "layout": "stacked_panes",
  "paneCount": 3,
  "dangerComments": [
    { "pane": 1, "line": 12, "text": "// don't touch", "glowFrame": 30 },
    { "pane": 1, "line": 28, "text": "// here be dragons", "glowFrame": 60 },
    { "pane": 2, "line": 8, "text": "// TODO: refactor this someday", "glowFrame": 100 },
    { "pane": 2, "line": 22, "text": "// nobody knows why this works", "glowFrame": 115 },
    { "pane": 3, "line": 15, "text": "// legacy — do not modify", "glowFrame": 140 }
  ],
  "scrollRate": 0.5,
  "narrationSegments": ["where_to_start_001"]
}
```

---
