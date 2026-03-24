[Remotion]

# Section 6.2: Legacy Codebase Reveal

**Tool:** Remotion
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 0:03 - 0:10

## Visual Description

A dense, intimidating codebase fills the screen. Rows of monospaced code scroll slowly upward — grays and muted blues. Interspersed throughout are the telltale signs of legacy software: comment lines reading `// don't touch`, `// here be dragons`, `// TODO: fix this someday`, `// nobody knows why this works`. These warning comments glow faintly in amber, standing out from the gray code mass.

The codebase is not one file — it's a mosaic of overlapping file panels, slightly offset, suggesting dozens of interconnected modules. File tabs along the top show names like `auth_handler.py`, `payment_processor.py`, `user_service.py`, `legacy_router.py`. The overall feeling is weight and complexity — real software, not a toy example.

A faint line count indicator in the bottom-right reads "~47,000 lines" in dim gray, reinforcing scale.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Code Panels (layered)
- 5 overlapping code panels, each 600x700px, staggered with 30px offsets
- Panel background: `#111827` at 0.9
- Panel border: 1px `#1E293B` at 0.3
- Panel border-radius: 8px
- Code text: JetBrains Mono, 11px, `#64748B` at 0.6 (generic code lines)
- Line numbers: JetBrains Mono, 11px, `#334155` at 0.3, left gutter 40px

#### Warning Comments (highlighted)
- `// don't touch` — JetBrains Mono, 11px, `#D9944A` at 0.8
- `// here be dragons` — JetBrains Mono, 11px, `#D9944A` at 0.8
- `// TODO: fix this someday` — JetBrains Mono, 11px, `#D9944A` at 0.7
- `// nobody knows why this works` — JetBrains Mono, 11px, `#D9944A` at 0.7
- Each has a subtle glow: 6px blur, `#D9944A` at 0.1

#### File Tabs
- 5 tabs across top of frontmost panel
- Tab background: `#1E293B` at 0.8
- Active tab: `#1F2937` with 2px top border `#60A5FA`
- Tab text: JetBrains Mono, 10px, `#94A3B8`
- Tab names: `auth_handler.py`, `payment_processor.py`, `user_service.py`, `legacy_router.py`, `config.py`

#### Line Count Indicator
- "~47,000 lines" — Inter, 13px, `#475569` at 0.3, positioned at (1780, 1040)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Panels fade in from black, layered front-to-back. Slight parallax — back panels appear first. `easeOutCubic`.
2. **Frame 30-60 (1-2s):** Code begins slow upward scroll (0.5px/frame). File tabs appear along top.
3. **Frame 60-90 (2-3s):** First warning comment `// don't touch` scrolls into view, glowing amber. Slight pulse.
4. **Frame 90-120 (3-4s):** `// here be dragons` appears in another panel. More amber warnings emerge.
5. **Frame 120-150 (4-5s):** Line count indicator fades in at bottom-right.
6. **Frame 150-210 (5-7s):** Hold. Code continues scrolling. Warning comments accumulate — the codebase feels alive, heavy, daunting.

### Typography
- Code: JetBrains Mono, 11px, `#64748B` at 0.6
- Warning comments: JetBrains Mono, 11px, `#D9944A` at 0.7-0.8
- Line numbers: JetBrains Mono, 11px, `#334155` at 0.3
- File tabs: JetBrains Mono, 10px, `#94A3B8`
- Line count: Inter, 13px, `#475569` at 0.3

### Easing
- Panel fade-in: `easeOut(cubic)` over 30 frames, staggered 5 frames apart
- Code scroll: `linear` at 0.5px/frame
- Warning comment glow: `easeInOut(sine)` pulse on 40-frame cycle
- Line count fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "Now — you don't work on a greenfield project. Nobody does. PDD can create prompts from existing code."

Segment: `where_to_start_001`

- **0:03** ("you don't work on a greenfield"): Legacy codebase panels fade in
- **0:05** ("Nobody does"): Warning comments begin glowing
- **0:07** ("PDD can create prompts"): Full codebase visible, line count shown — stage set for the transformation

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={210}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Layered code panels */}
    {panels.map((panel, i) => (
      <Sequence from={i * 5} key={i}>
        <FadeIn duration={30}>
          <CodePanel
            x={panel.x} y={panel.y}
            width={600} height={700}
            bgColor="#111827" borderColor="#1E293B"
            code={panel.lines}
            warningComments={panel.warnings}
            warningColor="#D9944A"
            scrollSpeed={0.5}
            lineNumberColor="#334155"
          />
        </FadeIn>
      </Sequence>
    ))}

    {/* File tabs */}
    <Sequence from={30}>
      <FadeIn duration={20}>
        <FileTabs
          tabs={["auth_handler.py", "payment_processor.py",
                 "user_service.py", "legacy_router.py", "config.py"]}
          activeIndex={0}
          activeColor="#60A5FA"
          bgColor="#1E293B"
          textColor="#94A3B8"
        />
      </FadeIn>
    </Sequence>

    {/* Line count */}
    <Sequence from={120}>
      <FadeIn duration={20}>
        <Text text="~47,000 lines" font="Inter" size={13}
          color="#475569" opacity={0.3} x={1780} y={1040} align="right" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_visualization",
  "chartId": "legacy_codebase_reveal",
  "panels": 5,
  "fileNames": [
    "auth_handler.py",
    "payment_processor.py",
    "user_service.py",
    "legacy_router.py",
    "config.py"
  ],
  "warningComments": [
    "// don't touch",
    "// here be dragons",
    "// TODO: fix this someday",
    "// nobody knows why this works"
  ],
  "lineCount": "~47,000",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_001"]
}
```

---
