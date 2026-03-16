[Remotion]

# Section 3.5: Five Generations + Z3 Formal Proof

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 14:16 – 14:38

## Visual Description
A two-phase visualization. Phase 1: Five code generation variants are shown side-by-side as narrow columns. Each contains slightly different generated code (stylized as abstract code blocks). A test suite runs against all five — three fail (red X marks), two pass (green checkmarks). The passing variant is selected and highlighted. The message: you don't need perfection on every run, just one pass out of N. Phase 2: Below, a formal verification callout appears. A Z3/SMT solver icon connects to a mathematical proof visualization — instead of sampling test cases, the system proves correctness for ALL inputs. A chip design analogy is drawn with a thin connecting line to "Synopsys Formality" label. This establishes PDD's connection to industrial formal verification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: None

### Chart/Visual Elements
- **Five generation columns (Phase 1):** Positioned across top half (y: 100–520)
  - Five columns at x: 200, 440, 680, 920, 1160 — each 200px wide, 360px tall
  - Each column: Rounded rectangle, `#1E293B` background, 1px border `rgba(255,255,255,0.1)`
  - Interior: Stylized code lines (6-8 horizontal bars per column, slightly varying lengths/positions)
  - Code line colors: `#6B7C93` at 0.4 opacity (neutral code)
  - Column headers: "v1", "v2", "v3", "v4", "v5" — `#8B9DC3`, 14px

- **Test results (overlay on each column):**
  - v1: ✗ — `#EF4444`, 36px, centered bottom of column
  - v2: ✓ — `#22C55E`, 36px, centered bottom
  - v3: ✗ — `#EF4444`, 36px
  - v4: ✗ — `#EF4444`, 36px
  - v5: ✓ — `#22C55E`, 36px

- **Selected variant highlight:** v2 column gets bright border `#22C55E` at 0.6 opacity, 2px. Other columns dim to 30% opacity.
- **Selection label:** "Pick the one that passes all tests." — `#FFFFFF` at 0.7, 16px, centered at (680, 560)
- **Walls reminder:** Small text: "The walls don't care how many attempts it took." — `#94A3B8`, 14px, y=590

- **Z3 Formal Verification (Phase 2, bottom half y: 620–960):**
  - Z3 logo/icon: Stylized "Z3" in a hexagonal chip outline, `#8B5CF6` (purple), centered at (500, 760)
  - Proof visualization: Grid of input dots (8×8 = 64 dots), all turning green simultaneously
    - Pre-proof: dots are `#6B7C93` at 0.3 (unknown)
    - Post-proof: all dots turn `#22C55E` at 0.7 (proven correct)
    - Label: "Every possible input" — `#22C55E`, 14px
  - Comparison callout at (1200, 760):
    - Top: "Testing: Samples N inputs" — `#D9944A`, with a partially-filled progress bar (30%)
    - Bottom: "Z3 Proof: ALL inputs verified" — `#22C55E`, with a fully-filled bar (100%)
  - Chip design connection: Thin dashed line from Z3 icon to label "Same technology as Synopsys Formality" — `#8B5CF6` at 0.4, 13px

### Animation Sequence
1. **Frame 0–45 (0–1.5s):** Five generation columns fade in from left to right with 8-frame stagger. Each column draws its code lines progressively (top→bottom). Column headers appear.
2. **Frame 45–120 (1.5–4.0s):** Test suite runs — a horizontal "scanning" bar sweeps top-to-bottom across all five columns simultaneously. As it passes, results appear: ✗ or ✓ at the bottom of each column. Failing columns get a brief red border flash; passing columns get green border flash. Synced with "Generate five versions. Pick the one that passes all tests."
3. **Frame 120–180 (4.0–6.0s):** v2 column zooms slightly (scale 1.0→1.05) and gets a solid green border. Other four columns shrink slightly (0.95) and dim to 30% opacity. Selection label fades in below.
4. **Frame 180–240 (6.0–8.0s):** "The walls don't care how many attempts it took." types on below selection label. Brief amber glow on all column borders (referencing walls).
5. **Frame 240–300 (8.0–10.0s):** Phase transition: generation columns slide up and compress to top 30% of screen. Z3 section begins. Z3 hexagonal icon draws on with purple glow.
6. **Frame 300–420 (10.0–14.0s):** Proof visualization: 64 dots appear in an 8×8 grid next to the Z3 icon. All dots are gray. Then simultaneously (over 30 frames), ALL dots flash to green. "Every possible input" label fades in. Contrasts with testing's partial coverage.
7. **Frame 420–510 (14.0–17.0s):** Comparison callout slides in on the right. Testing progress bar fills to ~30% (`#D9944A`). Z3 progress bar fills to 100% (`#22C55E`). Labels appear with each bar. Synced with "Not sampling. Mathematical proof."
8. **Frame 510–600 (17.0–20.0s):** Chip design connection: dashed line draws from Z3 icon outward. "Same technology as Synopsys Formality" label fades in at the end of the line. Synced with "The chip design analogy isn't a metaphor. It's the same technology."
9. **Frame 600–660 (20.0–22.0s):** Hold. Z3 proof grid pulses gently (green glow). All elements stable.

### Typography
- Column headers: Inter Medium, 14px, `#8B9DC3`
- Pass/fail marks: Inter Bold, 36px, respective colors
- Selection label: Inter Medium, 16px, `#FFFFFF` at 0.7 opacity
- Walls reminder: Inter Regular, 14px, `#94A3B8`
- Z3 icon text: Inter Black, 28px, `#8B5CF6`
- Proof label: Inter Medium, 14px, `#22C55E`
- Comparison labels: Inter Regular, 15px, respective colors
- Chip design label: Inter Regular, 13px, `#8B5CF6` at 0.6 opacity

### Easing
- Column fade-in: `easeOutQuad` (staggered)
- Test scan bar: linear (constant speed)
- Pass/fail marks: `spring({ damping: 10, stiffness: 150 })` (bouncy pop)
- Selected zoom: `easeOutCubic`
- Dimming: `easeOutQuad`
- Dot grid flash: `easeOutExpo` (all simultaneously, 300ms)
- Progress bar fill: `easeInOutCubic`
- Z3 icon draw: `easeInOutCubic`

## Narration Sync
> "Now, you might be thinking: 'But LLMs don't follow instructions reliably.' You're right. Today. But PDD doesn't need perfection on every run. Generate five versions. Pick the one that passes all tests. The walls don't care how many attempts it took."

> "And some of those walls aren't just tested — they're proven. PDD uses Z3, the same class of SMT solver that the chip industry uses for formal equivalence checking, to mathematically prove that properties hold for every possible input. Not sampling. Mathematical proof. The chip design analogy isn't a metaphor. It's the same technology."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Phase 1: Five generations */}
    <Sequence from={0} durationInFrames={240}>
      <FiveGenerationColumns
        variants={["v1", "v2", "v3", "v4", "v5"]}
        results={[false, true, false, false, true]}
        selectedIndex={1}
        stagger={8}
      />
    </Sequence>

    {/* Selection label */}
    <Sequence from={120} durationInFrames={120}>
      <FadeIn>
        <Label text="Pick the one that passes all tests." y={560} />
      </FadeIn>
      <Sequence from={60}>
        <TypeOnText text="The walls don't care how many attempts it took." y={590} />
      </Sequence>
    </Sequence>

    {/* Phase 2: Z3 Formal Proof */}
    <Sequence from={240} durationInFrames={60}>
      <SlideUp from={0.3}>
        <CompressedGenerations />
      </SlideUp>
    </Sequence>

    <Sequence from={300} durationInFrames={120}>
      <Z3Icon cx={500} cy={760} color="#8B5CF6" />
      <ProofDotGrid
        rows={8}
        cols={8}
        cx={700}
        cy={760}
        preColor="#6B7C93"
        postColor="#22C55E"
        flashFrame={30}
      />
    </Sequence>

    {/* Comparison callout */}
    <Sequence from={420} durationInFrames={90}>
      <ComparisonBars
        x={1200}
        y={760}
        testing={{ label: "Testing: Samples N inputs", fill: 0.3, color: "#D9944A" }}
        z3={{ label: "Z3 Proof: ALL inputs verified", fill: 1.0, color: "#22C55E" }}
      />
    </Sequence>

    {/* Chip design connection */}
    <Sequence from={510} durationInFrames={90}>
      <DashedConnector from={{ x: 540, y: 760 }} to={{ x: 900, y: 760 }} color="#8B5CF6" />
      <FadeIn>
        <Label
          text="Same technology as Synopsys Formality"
          color="#8B5CF6"
          opacity={0.6}
          x={900}
          y={780}
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "generations": {
    "count": 5,
    "results": [
      { "variant": "v1", "passes": false },
      { "variant": "v2", "passes": true },
      { "variant": "v3", "passes": false },
      { "variant": "v4", "passes": false },
      { "variant": "v5", "passes": true }
    ],
    "selected": "v2"
  },
  "z3": {
    "proofGrid": { "rows": 8, "cols": 8, "totalInputs": 64 },
    "comparison": {
      "testing": { "coverage": "~30%", "label": "Samples N inputs" },
      "formalProof": { "coverage": "100%", "label": "ALL inputs verified" }
    },
    "chipDesignAnalog": "Synopsys Formality"
  }
}
```

---
