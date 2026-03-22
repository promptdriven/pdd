[split:]

# Section 0.1: Split Screen Hook — Developer vs Grandmother

**Tool:** Split
**Duration:** ~5.5s (165 frames @ 30fps)
**Timestamp:** 0:00 - 0:05

## Visual Description

The video opens with a vertical split screen — the first image the viewer sees. No fade from black; it begins in media res.

**LEFT panel — "Modern Developer":** A developer at a keyboard, Cursor-style IDE visible on a large monitor. They make a slick AI-assisted edit — an inline suggestion appears and they accept it with a keystroke. The edit lands cleanly. The vibe is competent, modern, fast. Cool blue monitor glow lights their face.

**RIGHT panel — "1950s Grandmother":** A grandmother in a warm-lit parlor, carefully darning a wool sock by lamplight. Her hands are skilled, deliberate. A needle pulls thread through fabric. The work is careful and practiced. Warm amber lamplight dominates.

Both subjects complete their respective tasks simultaneously around the 3.5s mark — the code edit lands, the stitch finishes. The visual rhyme is the point: both are skilled at repair work.

The split line is a thin vertical divider at center. No labels — the visual tells the story.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black behind panels)
- Split line: 2px vertical divider at x: 960, color `#1E293B` at 0.15

### Chart/Visual Elements

#### Left Panel — Developer
- Source: Veo clip `developer_ai_edit` (see companion spec `02_developer_ai_edit.md`)
- Framing: medium-close on hands + monitor, face partially visible
- Color grade: cool blue `#4A90D9`, modern, sharp
- Content: IDE with inline AI suggestion appearing and being accepted

#### Right Panel — Grandmother
- Source: Veo clip `grandmother_darning` (see companion spec `03_grandmother_darning.md`)
- Framing: medium-close on hands + sock, face partially visible by lamplight
- Color grade: warm amber `#D9944A`, soft, nostalgic
- Content: hands darning a wool sock with needle and thread

#### Split Divider
- 2px vertical line at x: 960
- Color: `#1E293B` at 0.15
- Appears frame 0 — always present

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Hard cut in — both panels appear simultaneously. No fade from black. Immediate visual engagement.
2. **Frame 15-105 (0.5-3.5s):** Both clips play. Developer accepts AI suggestion. Grandmother pulls thread through sock. Actions are parallel.
3. **Frame 105-135 (3.5-4.5s):** Both complete their tasks simultaneously. Code edit lands cleanly. Stitch finishes neatly. The rhyme lands.
4. **Frame 135-165 (4.5-5.5s):** Brief hold. Both subjects pause. The parallel is established.

### Typography
- None in this spec — pure visual. No labels on panels.

### Easing
- Hard cut in: instant
- Clip playback: linear (natural video speed)
- No transitions within — holds through to next spec

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."
> "...you're getting really good at this."

Segments: `cold_open_001`, `cold_open_002`

- **0:00** ("If you use Cursor"): Split screen appears — developer working, grandmother darning
- **2.72s** (pause): Both continue working in parallel
- **3.46s** ("you're getting really good at this"): Both complete their tasks simultaneously
- **5.50s**: Hold — visual rhyme established

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={165}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Developer */}
    <Panel x={0} width={958}>
      <VeoClip
        clipId="developer_ai_edit"
        src="/clips/developer_ai_edit.mp4"
        fit="cover"
      />
      <ColorGrade color="#4A90D9" opacity={0.02} />
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#1E293B" opacity={0.15} width={2} />

    {/* Right panel — Grandmother */}
    <Panel x={962} width={958}>
      <VeoClip
        clipId="grandmother_darning"
        src="/clips/grandmother_darning.mp4"
        fit="cover"
      />
      <ColorGrade color="#D9944A" opacity={0.02} />
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "content": "veo_clip",
    "clipId": "developer_ai_edit",
    "colorGrade": "cool_blue",
    "gradeColor": "#4A90D9"
  },
  "rightPanel": {
    "content": "veo_clip",
    "clipId": "grandmother_darning",
    "colorGrade": "warm_amber",
    "gradeColor": "#D9944A"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["cold_open_001", "cold_open_002"]
}
```

---
