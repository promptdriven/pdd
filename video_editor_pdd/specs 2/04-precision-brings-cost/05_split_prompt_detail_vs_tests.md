[split:Prompt Detail vs Test Coverage] Prompt Precision vs Test Wall Split Screen

# Section 4.4: Split Screen — Prompt Detail vs Test Coverage

**Tool:** Remotion
**Duration:** ~12s
**Timestamp:** 0:20 - 0:32

## Visual Description
A split-screen comparison that divides the frame vertically. The left half is labeled "PROMPT DETAIL" with an amber-tinted document icon showing dense structured text — representing a highly detailed PDD prompt. The right half is labeled "TEST COVERAGE" with a green-tinted shield icon showing stacked test checkmarks — representing comprehensive test walls. A thin vertical divider separates the two halves with a subtle glow. Each side has a cost indicator: left shows "~2,000 tokens" and right shows "~45s feedback loop". The visual demonstrates that both sides of precision carry measurable cost. The panels slide in simultaneously from both edges, hold, then slide out.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Left panel: (0, 100) to (940, 980), semi-transparent dark backing
- Right panel: (980, 100) to (1920, 980), semi-transparent dark backing
- Divider: vertical line at x=960, 2px, glowing

### Chart/Visual Elements
- Left panel ("Prompt Detail"):
  - Background: rgba(245, 158, 11, 0.06) — faint amber tint
  - Header: "PROMPT DETAIL" in amber (#F59E0B)
  - Icon: simplified document silhouette with horizontal lines (text placeholder), #F59E0B at 30% opacity, 120px
  - Cost stat: "~2,000" in large white text
  - Cost unit: "tokens per prompt" in muted amber
  - Subtext: "structured, precise, repeatable" in #94A3B8
- Right panel ("Test Coverage"):
  - Background: rgba(34, 197, 94, 0.06) — faint green tint
  - Header: "TEST COVERAGE" in green (#22C55E)
  - Icon: shield with stacked checkmarks, #22C55E at 30% opacity, 120px
  - Cost stat: "~45s" in large white text
  - Cost unit: "feedback loop" in muted green
  - Subtext: "comprehensive, slow, reliable" in #94A3B8
- Divider: 2px vertical line, white at 40% opacity, soft glow
- Footer: "Both bring cost — both bring value" — centered across both panels, #CBD5E1

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Left panel slides in from left edge — translateX(-960)→translateX(0), opacity 0→1.
2. **Frame 0-25 (0-0.83s):** Right panel slides in from right edge — translateX(960)→translateX(0), opacity 0→1. (Simultaneous.)
3. **Frame 15-30 (0.5-1s):** Divider fades in — opacity 0→0.4, glow appears.
4. **Frame 25-45 (0.83-1.5s):** Left header "PROMPT DETAIL" and icon fade in.
5. **Frame 35-55 (1.17-1.83s):** Left cost stat "~2,000" and unit appear.
6. **Frame 45-65 (1.5-2.17s):** Right header "TEST COVERAGE" and icon fade in.
7. **Frame 55-75 (1.83-2.5s):** Right cost stat "~45s" and unit appear.
8. **Frame 70-90 (2.33-3s):** Footer text fades in.
9. **Frame 90-300 (3-10s):** Hold.
10. **Frame 300-360 (10-12s):** Both panels slide out — left to left, right to right. Divider fades.

### Typography
- Headers: Inter Black, 28px, uppercase, letter-spacing 0.15em
  - Left: #F59E0B
  - Right: #22C55E
- Cost stat numbers: Inter Black, 80px, #FFFFFF
- Cost units: Inter Medium, 24px
  - Left: #FCD34D (muted amber)
  - Right: #86EFAC (muted green)
- Subtext: Inter Regular, 18px, #94A3B8
- Footer: Inter SemiBold, 22px, #CBD5E1

### Easing
- Panel slides: `spring({ damping: 16, stiffness: 160 })`
- Text fades: `easeOutQuad`
- Panel slide out: `easeInCubic`

## Narration Sync
> "More detailed prompts mean slower generation. More comprehensive tests mean longer feedback cycles. This is the trade-off."

Left "Prompt Detail" panel appears as "more detailed prompts" is spoken. Right "Test Coverage" panel appears as "more comprehensive tests" is spoken. Footer emphasizes on "this is the trade-off."

## Code Structure (Remotion)
```typescript
<Sequence from={SPLIT_START} durationInFrames={360}>
  <AbsoluteFill>
    {/* Left panel — Prompt Detail */}
    <SplitPanel
      side="left"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 300, 360], [-960, 0, 0, -960])}px)`,
        opacity: interpolate(frame, [0, 25, 300, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="PROMPT DETAIL" color="#F59E0B" />
      <DocumentIcon color="#F59E0B" size={120} opacity={0.3} />
      <StatNumber value="~2,000" fontSize={80} />
      <StatDescriptor text="tokens per prompt" color="#FCD34D" />
      <SubText text="structured, precise, repeatable" />
    </SplitPanel>

    {/* Divider */}
    <VerticalDivider
      opacity={interpolate(frame, [15, 30, 300, 360], [0, 0.4, 0.4, 0])}
      glowColor="#FFFFFF"
    />

    {/* Right panel — Test Coverage */}
    <SplitPanel
      side="right"
      style={{
        transform: `translateX(${interpolate(frame, [0, 25, 300, 360], [960, 0, 0, 960])}px)`,
        opacity: interpolate(frame, [0, 25, 300, 360], [0, 1, 1, 0]),
      }}
    >
      <PanelHeader text="TEST COVERAGE" color="#22C55E" />
      <ShieldIcon color="#22C55E" size={120} opacity={0.3} />
      <StatNumber value="~45s" fontSize={80} />
      <StatDescriptor text="feedback loop" color="#86EFAC" />
      <SubText text="comprehensive, slow, reliable" />
    </SplitPanel>

    {/* Footer */}
    <FooterText
      text="Both bring cost — both bring value"
      opacity={interpolate(frame, [70, 90, 300, 360], [0, 1, 1, 0])}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "prompt_detail": {
    "stat": "~2,000",
    "unit": "tokens per prompt",
    "subtext": "structured, precise, repeatable",
    "color": "#F59E0B",
    "direction": "cost"
  },
  "test_coverage": {
    "stat": "~45s",
    "unit": "feedback loop",
    "subtext": "comprehensive, slow, reliable",
    "color": "#22C55E",
    "direction": "cost"
  },
  "footer": "Both bring cost — both bring value",
  "totalFrames": 360,
  "fps": 30
}
```

---
