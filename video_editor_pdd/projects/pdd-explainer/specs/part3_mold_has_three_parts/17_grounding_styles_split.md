[split:]

# Section 3.17: Grounding Styles — OOP vs Functional Output

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 4:00 - 4:14

## Visual Description

A split screen showing how the same prompt and tests, with different grounding contexts, produce code in dramatically different styles.

**LEFT — "OOP Grounding":** A code panel showing classes with methods — inheritance, encapsulation, `self.` references. The code is syntax-highlighted with a subtle blue tint. Label: "Path A: OOP codebase grounding". A small icon of structured crystalline blue material.

**RIGHT — "Functional Grounding":** A code panel showing pure functions with composition — `map`, `filter`, list comprehensions, no classes. The code has a subtle green-gold tint. Label: "Path B: Functional codebase grounding". A small icon of flowing organic green material.

Above both: "Same prompt. Same tests. Different grounding." The point: grounding determines the style of the output without changing the behavior.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Shared Header
- "Same prompt. Same tests." — Inter, 16px, `#94A3B8` at 0.6, centered at y: 40
- "Different grounding." — Inter, 16px, bold, `#A78BFA` at 0.7, centered at y: 65

#### Left Panel — OOP
- Header: "OOP GROUNDING" — Inter, 16px, bold, `#4A90D9` at 0.7, y: 110
- Material icon: crystalline blue dot, 12px, `#4A90D9` at 0.4
- Code panel: 850×650px, bg `#1E1E2E`, border `#4A90D9` at 0.2
- Code: JetBrains Mono, 10px, syntax-highlighted — classes, methods, `self.`
- Path label: "Path A: OOP codebase grounding" — Inter, 12px, `#4A90D9` at 0.5, y: 830

#### Right Panel — Functional
- Header: "FUNCTIONAL GROUNDING" — Inter, 16px, bold, `#4ADE80` at 0.7, y: 110
- Material icon: organic green dot, 12px, `#4ADE80` at 0.4
- Code panel: 850×650px, bg `#1E1E2E`, border `#4ADE80` at 0.2
- Code: JetBrains Mono, 10px, syntax-highlighted — pure functions, composition
- Path label: "Path B: Functional codebase grounding" — Inter, 12px, `#4ADE80` at 0.5, y: 830

#### Bottom
- "Both pass all tests. ✓" — Inter, 14px, bold, `#4ADE80` at 0.6, centered at y: 920

### Animation Sequence
1. **Frame 0-30 (0-1s):** Shared header fades in. Split line appears.
2. **Frame 30-120 (1-4s):** Left panel: OOP code types in line by line. Header and material icon visible.
3. **Frame 120-240 (4-8s):** Right panel: Functional code types in. Visually distinct style is immediately apparent.
4. **Frame 240-330 (8-11s):** Path labels appear on both sides. Both panels fully visible.
5. **Frame 330-420 (11-14s):** "Both pass all tests. ✓" appears at bottom. Hold.

### Typography
- Shared header: Inter, 16px, `#94A3B8` / bold `#A78BFA`
- Panel headers: Inter, 16px, bold (700), respective colors
- Code: JetBrains Mono, 10px, syntax-highlighted
- Path labels: Inter, 12px, respective colors at 0.5
- Bottom: Inter, 14px, bold (700), `#4ADE80` at 0.6

### Easing
- Header fade: `easeOut(quad)` over 15 frames
- Code type-in: stagger 1 frame per line, `easeOut(quad)`
- Path labels: `easeOut(quad)` over 15 frames
- Bottom text: `easeOut(quad)` over 20 frames

## Narration Sync
> "Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system."
> "Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it automatically to future generations."

Segments: `part3_mold_has_three_parts_024`, `part3_mold_has_three_parts_025`

- **4:00** ("Grounding is learned"): Split screen appears, both code panels building
- **4:07** ("Your style. Your patterns"): Both panels complete, bottom label

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Shared header */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <Text text="Same prompt. Same tests." font="Inter" size={16}
          color="#94A3B8" opacity={0.6} x={960} y={40} align="center" />
        <Text text="Different grounding." font="Inter" size={16}
          weight={700} color="#A78BFA" opacity={0.7}
          x={960} y={65} align="center" />
      </FadeIn>
    </Sequence>

    {/* Left: OOP */}
    <Panel x={0} width={958}>
      <Sequence from={30}>
        <CodeTypeIn code={OOP_CODE} font="JetBrains Mono" fontSize={10}
          bg="#1E1E2E" border="#4A90D9"
          stagger={1} header="OOP GROUNDING" headerColor="#4A90D9" />
      </Sequence>
    </Panel>

    <SplitLine x={960} color="#334155" opacity={0.15} width={2} />

    {/* Right: Functional */}
    <Panel x={962} width={958}>
      <Sequence from={120}>
        <CodeTypeIn code={FUNC_CODE} font="JetBrains Mono" fontSize={10}
          bg="#1E1E2E" border="#4ADE80"
          stagger={1} header="FUNCTIONAL GROUNDING" headerColor="#4ADE80" />
      </Sequence>
    </Panel>

    {/* Bottom */}
    <Sequence from={330}>
      <FadeIn duration={20}>
        <Text text="Both pass all tests. ✓" font="Inter" size={14}
          weight={700} color="#4ADE80" opacity={0.6}
          x={960} y={920} align="center" />
      </FadeIn>
    </Sequence>
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
    "header": "OOP GROUNDING",
    "headerColor": "#4A90D9",
    "content": "oop_code",
    "pathLabel": "Path A: OOP codebase grounding",
    "thematicRole": "object_oriented_style"
  },
  "rightPanel": {
    "header": "FUNCTIONAL GROUNDING",
    "headerColor": "#4ADE80",
    "content": "functional_code",
    "pathLabel": "Path B: Functional codebase grounding",
    "thematicRole": "functional_style"
  },
  "sharedHeader": "Same prompt. Same tests. Different grounding.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_024", "part3_mold_has_three_parts_025"]
}
```

---
