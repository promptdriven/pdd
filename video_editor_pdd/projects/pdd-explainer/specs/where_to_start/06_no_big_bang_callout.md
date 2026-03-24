[title:]

# Section 6.6: No Big Bang Callout

**Tool:** Title
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:26 - 0:29

## Visual Description

A text callout card that bridges the "where to start" section into the closing. The network graph from the previous shot fades into the background at very low opacity, and a clean typographic statement appears center-screen:

> "You don't patch socks because socks got cheap."

This is the sock metaphor returning one final time — not as a visual but as a text punch. The quote sits in large, serif-adjacent typography (Inter at heavy weight with wider tracking for a more editorial feel). Below, a thin horizontal rule, and then a smaller line: "The economics made patching irrational."

The callback is intentional — this exact phrasing mirrors the opening of the closing section, creating a smooth handoff.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Background Ghost (network echo)
- Faint echo of the module network graph from 05
- All nodes: `#1E293B` at 0.03
- All edges: `#334155` at 0.02
- Fades from 0.03 → 0.0 over first 30 frames

#### Primary Quote
- "You don't patch socks" — Inter, 44px, bold (700), `#E2E8F0` at 0.9, centered at y: 460
- "because socks got cheap." — Inter, 44px, bold (700), `#D9944A` at 0.9, centered at y: 520
- The amber color on "because socks got cheap" echoes the sock/grandmother color palette

#### Horizontal Rule
- 160px wide, 1.5px, `#334155` at 0.4, centered at y: 560

#### Secondary Line
- "The economics made patching irrational." — Inter, 20px, regular (400), `#94A3B8` at 0.6, centered at y: 590

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background ghost fades. Clean dark background.
2. **Frame 15-35 (0.5-1.17s):** "You don't patch socks" fades in. `easeOutQuad`.
3. **Frame 35-50 (1.17-1.67s):** "because socks got cheap." fades in with 8px upward slide, in amber. `easeOutCubic`.
4. **Frame 50-58 (1.67-1.93s):** Horizontal rule draws from center outward. `easeInOutQuad`.
5. **Frame 58-70 (1.93-2.33s):** Secondary line fades in. `easeOutQuad`.
6. **Frame 70-90 (2.33-3s):** Hold. Clean and impactful.

### Typography
- Primary quote line 1: Inter, 44px, bold (700), `#E2E8F0` at 0.9
- Primary quote line 2: Inter, 44px, bold (700), `#D9944A` at 0.9
- Horizontal rule: `#334155` at 0.4
- Secondary line: Inter, 20px, regular (400), `#94A3B8` at 0.6

### Easing
- Quote line 1 fade: `easeOut(quad)` over 20 frames
- Quote line 2 slide-up: `easeOut(cubic)` over 15 frames
- Rule draw: `easeInOut(quad)` over 8 frames
- Secondary line fade: `easeOut(quad)` over 12 frames
- Ghost network fade: `easeIn(quad)` over 30 frames

## Narration Sync
> "You don't patch socks because socks got cheap. The economics made patching irrational."

Segment: `where_to_start_003`

- **0:26** ("You don't patch socks"): First line appears
- **0:27** ("because socks got cheap"): Amber text slides up
- **0:28** ("The economics"): Rule draws, secondary line fades in
- **0:29** (hold): Clean frame — the callback lands

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Ghost network echo */}
    <Sequence from={0} durationInFrames={30}>
      <FadeOut duration={30}>
        <GhostNetwork nodes={networkNodes} edges={networkEdges}
          nodeOpacity={0.03} edgeOpacity={0.02} />
      </FadeOut>
    </Sequence>

    {/* Primary quote - line 1 */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="You don't patch socks"
          font="Inter" size={44} weight={700}
          color="#E2E8F0" opacity={0.9}
          x={960} y={460} align="center" />
      </FadeIn>
    </Sequence>

    {/* Primary quote - line 2 (amber) */}
    <Sequence from={35}>
      <SlideUp distance={8} duration={15}>
        <FadeIn duration={15}>
          <Text text="because socks got cheap."
            font="Inter" size={44} weight={700}
            color="#D9944A" opacity={0.9}
            x={960} y={520} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={50}>
      <DrawLine from={[880, 560]} to={[1040, 560]}
        color="#334155" opacity={0.4} width={1.5}
        drawDuration={8} fromCenter />
    </Sequence>

    {/* Secondary line */}
    <Sequence from={58}>
      <FadeIn duration={12}>
        <Text text="The economics made patching irrational."
          font="Inter" size={20} weight={400}
          color="#94A3B8" opacity={0.6}
          x={960} y={590} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "quote_card",
  "chartId": "no_big_bang_callout",
  "quoteLine1": "You don't patch socks",
  "quoteLine2": "because socks got cheap.",
  "quoteLine2Color": "#D9944A",
  "secondaryText": "The economics made patching irrational.",
  "callback": "sock_metaphor",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_003"]
}
```

---
