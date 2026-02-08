# Section 6.2: Sock Metaphor Returns -- Final Callback

**Tool:** Hybrid (Video + Remotion overlay)
**Duration:** ~15 seconds
**Timestamp:** 20:25 - 20:40

## Visual Description

The sock metaphor returns one final time. A holey sock is visible. A person considers it for a moment, then discards it and grabs a fresh one. This is the closing callback to the cold open -- the economics argument made visceral and personal. The audience should feel the "of course you wouldn't patch it" instinct.

## Video Base

### Veo 3.1 Prompt

```
A person holding a worn sock with a visible hole. They look at it briefly, then casually toss it into a wastebasket. They reach to the side and pick up a brand new, fresh sock from a pack.

SUBJECT:
- Adult person (any gender), casual clothing
- Worn sock with visible hole held in one hand
- Wastebasket nearby
- Pack of new socks within reach

ACTION:
- Hold up holey sock, brief examination (2 seconds)
- Shrug or dismissive expression
- Toss sock into wastebasket (casual, not dramatic)
- Reach to side, grab fresh sock from pack
- Brief satisfied look

ENVIRONMENT:
- Modern bedroom or laundry room
- Clean, well-lit
- Warm neutral tones
- Simple, uncluttered

CAMERA:
- Medium shot, upper body and hands visible
- Slight dolly or static
- Eye level

MOOD: Casual, obvious. This is a trivial decision -- not even worth thinking about.

DURATION: 15 seconds
NO TEXT OVERLAY (Remotion will add)
```

## Remotion Overlay Specifications

### Canvas
- Resolution: 1920x1080
- Overlay on video base
- Minimal overlay -- the video carries this scene

### Overlay Elements

1. **Cost Label (Brief)**
   - Small, understated text: "$0.50" near the sock as it is held up
   - Fades in at 1s, fades out at 3s
   - Color: White at 60% opacity
   - Font: Monospace, 18px
   - Callback to Section 1 economics charts

2. **Subtle "Crumple" Particle Effect**
   - When sock is tossed, a few particles trail it
   - 10-15 small particles, gray
   - Quick dissipation (0.5s)
   - Reinforces "disposable" feeling

3. **Fresh Sock Subtle Glow**
   - When fresh sock is grabbed, very brief warm glow
   - Color: Soft white with slight amber tint
   - Duration: 0.3s pulse
   - Indicates "new, cheap, replaceable"

### Visual Design

```
┌──────────────────────────────────────────────────────────┐
│                                                          │
│              ┌──────────────────────┐                    │
│              │                      │                    │
│              │   Person holds up    │                    │
│              │   holey sock         │                    │
│              │                      │  $0.50             │
│              │   → considers →      │                    │
│              │   → discards →       │                    │
│              │   → grabs fresh →    │                    │
│              │                      │                    │
│              └──────────────────────┘                    │
│                                                          │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Sock examination
   - Video: Person holds up holey sock
   - Overlay: "$0.50" fades in near sock
   - Brief, not belabored

2. **Frame 60-120 (2-4s):** Decision moment
   - Video: Person considers, shrugs
   - Overlay: "$0.50" fades out
   - The decision is obvious

3. **Frame 120-240 (4-8s):** Discard
   - Video: Sock tossed into wastebasket
   - Overlay: Subtle particle trail on the toss arc
   - Sound: Soft "crumple"

4. **Frame 240-360 (8-12s):** Grab fresh
   - Video: Hand reaches for new sock
   - Overlay: Brief warm glow on fresh sock
   - The replacement is trivial

5. **Frame 360-450 (12-15s):** Hold satisfied
   - Video: Person with fresh sock, satisfied
   - Overlay: None -- let the video breathe
   - The point is made

### Code Structure (Remotion)

```typescript
const SockMetaphorFinal: React.FC = () => {
  const frame = useCurrentFrame();

  // Cost label fade
  const costLabelOpacity = interpolate(
    frame,
    [15, 30, 60, 90],
    [0, 0.6, 0.6, 0],
    { extrapolateRight: 'clamp' }
  );

  // Particle trail (during toss)
  const showParticles = frame >= 120 && frame <= 180;
  const particleProgress = interpolate(
    frame,
    [120, 180],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Fresh sock glow
  const freshGlow = interpolate(
    frame,
    [260, 280, 300, 320],
    [0, 0.5, 0.5, 0],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill>
      {/* Video base layer */}
      <Video src="sock_discard_final.mp4" />

      {/* Cost label */}
      <div style={{
        position: 'absolute',
        right: 280,
        top: 200,
        opacity: costLabelOpacity,
        fontFamily: 'monospace',
        fontSize: 18,
        color: 'rgba(255, 255, 255, 0.6)',
      }}>
        $0.50
      </div>

      {/* Particle trail on toss */}
      {showParticles && (
        <CrumpleParticles
          progress={particleProgress}
          count={12}
          startX={600}
          startY={400}
          endX={800}
          endY={600}
        />
      )}

      {/* Fresh sock glow */}
      <div style={{
        position: 'absolute',
        left: 500,
        top: 300,
        width: 200,
        height: 150,
        borderRadius: '50%',
        background: `radial-gradient(circle, rgba(255, 240, 220, ${freshGlow * 0.3}), transparent)`,
        pointerEvents: 'none',
      }} />
    </AbsoluteFill>
  );
};
```

### Easing

- Cost label: `easeInOutQuad` (gentle appear/disappear)
- Particles: `easeOutQuad` (scatter and fade)
- Fresh glow: `easeOutCubic` (soft pulse)

## Narration Sync

> "You don't patch socks because socks got cheap. The economics made patching irrational."

"You don't patch socks" lands as the person holds the holey sock. "Socks got cheap" hits during the discard. "Economics made patching irrational" plays over the fresh sock grab -- the action illustrates the narration perfectly.

## Audio Notes

- Subtle "crumple" sound when sock is tossed (per script sound design notes)
- Brief, satisfying rustle when fresh sock is grabbed
- No dramatic music -- this is a casual, everyday moment
- The understated audio reinforces the "obvious" feeling

## Visual Style Notes

- This is a CALLBACK to the Cold Open (Section 0) -- same metaphor, now with full context
- The video should feel natural and unforced
- Overlays are minimal -- the video carries the emotional weight
- The "$0.50" cost label ties back to Section 1 economics
- The person's expression should convey "why would I even consider patching this?"
- Warm, domestic color grading -- NOT the sepia of Section 1

## Continuity Notes

- The sock from the Cold Open was darned by the grandmother
- This time, the sock is simply discarded -- the paradigm has shifted
- The audience should feel the contrast without it being stated

## Transition

Cuts to Section 6.3, where the same logic is applied to code: a developer adds a test and regenerates instead of patching.
