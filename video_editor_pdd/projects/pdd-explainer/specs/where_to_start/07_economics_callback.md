[Remotion]

# Section 6.7: Economics Callback — Sock Metaphor Returns

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:26 - 0:32

## Visual Description

The section's closing beat — a callback to the opening sock metaphor that bookends the entire video. The text-forward layout clears, and a simple, powerful visual comparison appears.

**Left side:** A stylized sock with a visible hole — the same visual language from Part 1. Below it, a label: "patch it?" The sock is rendered in warm tones (`#D9944A` outline) on a dim background. A needle and thread icon sits beside it, suggesting the old approach.

**Right side:** A fresh, clean sock — solid outline, no holes, pristine. Below it, a label: "replace it." The sock glows faintly green (`#10B981` outline), suggesting the new economics.

Between them, a crossed-out "→" from left to right and a bold "→" below it, indicating the shift. The old approach (patch) is crossed out. The new approach (replace/regenerate) is the clear winner.

Below the comparison, the closing statement appears: **"You don't patch socks because socks got cheap."** — with "got cheap" in the warm amber of the economics palette.

Then: **"The economics made patching irrational."** — clean, final, authoritative.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Holey Sock (Left)
- SVG sock outline: ~160x200px, `#D9944A` 2px stroke, no fill
- Visible hole: irregular gap in the outline near the heel, `#0A0F1A` showing through
- Needle + thread icon: 30x30px, `#D9944A` at 0.4, positioned upper-right of sock
- Position: centered at x: 450, y: 380

#### Fresh Sock (Right)
- SVG sock outline: ~160x200px, `#10B981` 2px stroke, no fill
- Complete, pristine — no holes
- Subtle glow: `#10B981` at 0.06, 12px blur
- Position: centered at x: 1470, y: 380

#### Labels
- "patch it?" — Inter, 18px, `#D9944A` at 0.6, centered below left sock, y: 520
- "replace it." — Inter, 18px, semi-bold, `#10B981` at 0.8, centered below right sock, y: 520

#### Transition Arrow
- Crossed-out arrow: `#EF4444` at 0.3, from (600, 390) to (1300, 390), with red X through it
- Bold arrow below: `#10B981` at 0.6, 2px, from (600, 420) to (1300, 420)

#### Closing Statements
- Line 1: "You don't patch socks because socks got cheap." — Inter, 28px, `#E2E8F0` at 0.9, centered at y: 680
  - "got cheap" highlighted in `#D9944A`
- Line 2: "The economics made patching irrational." — Inter, 22px, `#94A3B8` at 0.7, centered at y: 730

### Animation Sequence
1. **Frame 0-30 (0-1s):** Holey sock fades in on the left. Needle icon appears.
2. **Frame 30-50 (1-1.67s):** Fresh sock fades in on the right with subtle green glow.
3. **Frame 50-70 (1.67-2.33s):** Labels appear: "patch it?" and "replace it."
4. **Frame 70-90 (2.33-3s):** Crossed-out arrow draws, then bold green arrow draws below it.
5. **Frame 90-120 (3-4s):** Line 1 appears: "You don't patch socks because socks got cheap." with "got cheap" highlighting in amber.
6. **Frame 120-150 (4-5s):** Line 2 appears: "The economics made patching irrational."
7. **Frame 150-180 (5-6s):** Hold. Fresh sock pulses gently. All elements visible. Section resolves.

### Typography
- Labels: Inter, 18px; left at 0.6, right at semi-bold 0.8
- Closing line 1: Inter, 28px, `#E2E8F0` at 0.9, "got cheap" in `#D9944A`
- Closing line 2: Inter, 22px, `#94A3B8` at 0.7

### Easing
- Sock fade-in: `easeOut(quad)` over 20 frames each
- Label appear: `easeOut(quad)` over 15 frames
- Arrow draw: `easeInOut(quad)` over 15 frames
- Cross-out: `easeOut(cubic)` over 10 frames
- Text lines: `easeOut(cubic)` over 20 frames
- Fresh sock pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

Segment: `where_to_start_003`

- **0:26** (26.24s): Sock comparison appears — "You don't patch socks"
- **0:28** (28.00s): Labels and arrows — "because socks got cheap"
- **0:30** (30.00s): Closing statements — "The economics made patching irrational"
- **0:32** (32.08s): Hold, section ends

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Holey sock */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <SockOutline
          x={450} y={380} width={160} height={200}
          color="#D9944A" strokeWidth={2}
          hole={{ position: "heel", size: 30 }}
        />
        <NeedleIcon x={540} y={310} size={30}
          color="#D9944A" opacity={0.4} />
      </FadeIn>
    </Sequence>

    {/* Fresh sock */}
    <Sequence from={30}>
      <FadeIn duration={20}>
        <SockOutline
          x={1470} y={380} width={160} height={200}
          color="#10B981" strokeWidth={2}
          glow={{ color: "#10B981", opacity: 0.06, radius: 12 }}
          pulseCycle={50}
        />
      </FadeIn>
    </Sequence>

    {/* Labels */}
    <Sequence from={50}>
      <FadeIn duration={15}>
        <Text text="patch it?" font="Inter" size={18}
          color="#D9944A" opacity={0.6}
          x={450} y={520} align="center" />
        <Text text="replace it." font="Inter" size={18}
          weight={600} color="#10B981" opacity={0.8}
          x={1470} y={520} align="center" />
      </FadeIn>
    </Sequence>

    {/* Crossed-out arrow + green arrow */}
    <Sequence from={70}>
      <DrawArrow from={{ x: 600, y: 390 }} to={{ x: 1300, y: 390 }}
        color="#EF4444" opacity={0.3} width={1.5}
        drawDuration={15} />
      <Sequence from={10}>
        <CrossOut from={{ x: 900, y: 375 }} to={{ x: 1000, y: 405 }}
          color="#EF4444" opacity={0.5} duration={10} />
      </Sequence>
      <Sequence from={15}>
        <DrawArrow from={{ x: 600, y: 420 }} to={{ x: 1300, y: 420 }}
          color="#10B981" opacity={0.6} width={2}
          drawDuration={15} />
      </Sequence>
    </Sequence>

    {/* Closing line 1 */}
    <Sequence from={90}>
      <FadeIn duration={20}>
        <RichText x={960} y={680} align="center" font="Inter" size={28}>
          <Span color="#E2E8F0" opacity={0.9}>
            You don't patch socks because socks{' '}
          </Span>
          <Span color="#D9944A" weight={600}>got cheap</Span>
          <Span color="#E2E8F0" opacity={0.9}>.</Span>
        </RichText>
      </FadeIn>
    </Sequence>

    {/* Closing line 2 */}
    <Sequence from={120}>
      <FadeIn duration={20}>
        <Text text="The economics made patching irrational."
          font="Inter" size={22} color="#94A3B8" opacity={0.7}
          x={960} y={730} align="center" />
      </FadeIn>
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "metaphor_callback",
  "comparison": {
    "left": {
      "label": "patch it?",
      "icon": "holey_sock",
      "color": "#D9944A",
      "status": "deprecated"
    },
    "right": {
      "label": "replace it.",
      "icon": "fresh_sock",
      "color": "#10B981",
      "status": "preferred"
    }
  },
  "closingStatements": [
    "You don't patch socks because socks got cheap.",
    "The economics made patching irrational."
  ],
  "narrationSegments": ["where_to_start_003"]
}
```

---
