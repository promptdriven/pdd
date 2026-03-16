[Remotion]

# Section 2.10: PDD Morph — Same Transition, For Software

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 10:43 - 10:53

## Visual Description
A three-element morph sequence explicitly maps the chip industry's architecture onto PDD. Three items sit in a horizontal row: LEFT — a Verilog code document, CENTER — a gate-level netlist thumbnail, RIGHT — a Synopsys verification checkmark badge. In a synchronized morph, all three transform: the Verilog document reshapes into a glowing prompt file (amber border), the netlist thumbnail dissolves into lines of software code (blue-gray), and the verification badge stays but its label changes from "Formal Verification" to "Test Suite." The morph is smooth and deliberate — each element cross-fades and reshapes simultaneously. Below, a single-line label types in: "This is that same transition. For software."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Element A — Spec (Left)**
  - Position: centered at (320, 420)
  - Before: Rounded rectangle 280px x 340px, border `#94A3B8` 1.5px, fill `rgba(148,163,184,0.05)`
    - Header: "Verilog HDL" — `#94A3B8`, 16px, bold
    - Icon: Code brackets with `module` keyword, `#94A3B8`
  - After: Same rectangle, border morphs to `#D9944A`, fill to `rgba(217,148,74,0.05)`
    - Header: "PROMPT" — `#D9944A`, 16px, bold
    - Icon: Document with natural language lines, `#D9944A`
  - Glow after morph: `rgba(217,148,74,0.1)` radial, radius 180px
- **Element B — Output (Center)**
  - Position: centered at (960, 420)
  - Before: Rounded rectangle 280px x 340px, border `#4A90D9` 1.5px, fill `rgba(74,144,217,0.05)`
    - Header: "Gate-Level Netlist" — `#4A90D9`, 16px, bold
    - Content: Dense tiny gate symbols, `#4A90D9` at 0.3
  - After: Same rectangle, border stays `#4A90D9`, fill stays
    - Header: "Generated Code" — `#4A90D9`, 16px, bold
    - Content: Code line representations (horizontal bars), `#4A90D9` at 0.5
- **Element C — Verification (Right)**
  - Position: centered at (1600, 420)
  - Before: Circle 120px diameter, fill `#2AA198`, white checkmark icon
    - Label below: "Formal Verification" — `#2AA198`, 14px
  - After: Same circle, same checkmark — unchanged
    - Label below: "Test Suite" — `#2AA198`, 14px (cross-fades)
- **Connecting Arrows**
  - Arrow from A to B: `rgba(255,255,255,0.2)`, 1.5px, with small arrowhead
  - Arrow from B to C: `rgba(255,255,255,0.2)`, 1.5px, with small arrowhead
  - Labels on arrows: "generates" (A→B), "verifies" (B→C) — `#94A3B8`, 12px
- **Bottom Label**
  - Centered at (960, 860)
  - Text: "This is that same transition. For software." — `#FFFFFF`, 24px, bold

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** All three "before" elements fade in simultaneously. Connecting arrows draw left-to-right. Arrow labels appear
2. **Frame 40-80 (1.33-2.67s):** Hold on the chip-industry diagram (Verilog → Netlist → Verification)
3. **Frame 80-160 (2.67-5.33s):** Synchronized morph:
   - Element A: Border color cross-fades `#94A3B8` → `#D9944A`. Header cross-fades "Verilog HDL" → "PROMPT". Icon morphs. Glow radiates
   - Element B: Header cross-fades "Gate-Level Netlist" → "Generated Code". Content morphs from gates to code lines
   - Element C: Badge stays static (checkmark unchanged). Label cross-fades "Formal Verification" → "Test Suite"
   - Arrow labels stay unchanged
4. **Frame 160-220 (5.33-7.33s):** Hold on the PDD diagram. All three elements settle at full opacity
5. **Frame 220-270 (7.33-9s):** Bottom label types in character by character
6. **Frame 270-300 (9-10s):** Hold at final state

### Typography
- Element Headers: Inter, 16px, bold (700), respective element colors
- Arrow Labels: Inter, 12px, regular (400), `#94A3B8`
- Verification Label: Inter, 14px, medium (500), `#2AA198`
- Bottom Label: Inter, 24px, bold (700), `#FFFFFF`

### Easing
- Elements fade-in: `easeOut(quad)`
- Arrow draw: `easeOut(cubic)`
- Morph cross-fade (all elements): `easeInOut(cubic)` over 80 frames
- Glow radiate: `easeOut(quad)`
- Bottom label typewriter: `linear`

## Narration Sync
> "This is that same transition. For software."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Before State — Chip Industry */}
  <Sequence from={0} durationInFrames={80}>
    <SpecElement
      x={320} y={420} width={280} height={340}
      header="Verilog HDL" icon="verilog"
      borderColor="#94A3B8"
    />
    <OutputElement
      x={960} y={420} width={280} height={340}
      header="Gate-Level Netlist" content="gates"
      borderColor="#4A90D9"
    />
    <VerificationBadge
      x={1600} y={420} diameter={120}
      color="#2AA198" label="Formal Verification"
    />
    <ConnectingArrows
      positions={[320, 960, 1600]}
      labels={["generates", "verifies"]}
    />
  </Sequence>

  {/* Morph Transition */}
  <Sequence from={80} durationInFrames={80}>
    <MorphTransition
      specMorph={{ headerTo: "PROMPT", borderTo: "#D9944A", iconTo: "prompt" }}
      outputMorph={{ headerTo: "Generated Code", contentTo: "codeLines" }}
      verifyMorph={{ labelTo: "Test Suite" }}
    />
  </Sequence>

  {/* Bottom Label */}
  <Sequence from={220} durationInFrames={50}>
    <TypewriterLabel
      text="This is that same transition. For software."
      x={960} y={860} color="#FFFFFF" fontSize={24}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "elements": {
    "spec": {
      "position": { "x": 320, "y": 420 },
      "size": { "width": 280, "height": 340 },
      "before": {
        "header": "Verilog HDL",
        "borderColor": "#94A3B8",
        "icon": "verilog"
      },
      "after": {
        "header": "PROMPT",
        "borderColor": "#D9944A",
        "icon": "prompt",
        "glowColor": "rgba(217,148,74,0.1)"
      }
    },
    "output": {
      "position": { "x": 960, "y": 420 },
      "size": { "width": 280, "height": 340 },
      "before": {
        "header": "Gate-Level Netlist",
        "content": "gates",
        "borderColor": "#4A90D9"
      },
      "after": {
        "header": "Generated Code",
        "content": "codeLines",
        "borderColor": "#4A90D9"
      }
    },
    "verification": {
      "position": { "x": 1600, "y": 420 },
      "diameter": 120,
      "color": "#2AA198",
      "before": { "label": "Formal Verification" },
      "after": { "label": "Test Suite" }
    }
  },
  "arrows": {
    "labels": ["generates", "verifies"],
    "color": "rgba(255,255,255,0.2)"
  },
  "bottomLabel": {
    "text": "This is that same transition. For software.",
    "color": "#FFFFFF"
  }
}
```

---
