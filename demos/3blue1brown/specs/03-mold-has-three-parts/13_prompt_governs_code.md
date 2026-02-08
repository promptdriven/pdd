# Section 3.13: Prompt Governs Code

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 14:00 - 14:15

## Visual Description

The prompt glows brightly. It's small -- maybe 10-15 lines. But it governs a 200-line code file shown beside it. A ratio appears: "1:5 to 1:10". This visualizes the leverage: a small specification controls a large implementation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Side-by-side comparison layout

### Animation Elements

1. **Prompt Document (Left)**
   - Small, compact (10-15 lines)
   - Blue glow (#4A90D9)
   - Pulsing with authority
   - Line counter: "15 lines"

2. **Code File (Right)**
   - Large, scrolling (200+ lines implied)
   - Gray text, no glow
   - Minimap showing full extent
   - Line counter: "~200 lines"

3. **Size Comparison**
   - Visual ratio emphasized
   - Arrows showing "governs" relationship
   - Ratio indicator: "1:5 to 1:10"

4. **Dominance Indicator**
   - Prompt glows brighter
   - Code is subordinate (visually)
   - Value hierarchy clear

### Animation Sequence

1. **Frame 0-90 (0-3s):** Prompt appears
   - Small prompt document enters
   - Blue glow activates
   - "15 lines" counter

2. **Frame 90-180 (3-6s):** Code appears
   - Large code file enters
   - Scrolls to show extent
   - "~200 lines" counter
   - Gray, not glowing

3. **Frame 180-270 (6-9s):** Comparison emphasis
   - Size ratio visually clear
   - "governs" arrow or connection
   - Prompt pulses

4. **Frame 270-360 (9-12s):** Ratio highlight
   - "1:5 to 1:10" ratio text appears
   - Prompt is clearly the source of truth
   - Code is derived output

5. **Frame 360-450 (12-15s):** Hold on relationship
   - Prompt continues glowing
   - Code is present but secondary
   - Clear hierarchy established

### Visual Design: Size Comparison

```
┌─────────────────┬───────────────────────────────────┐
│                 │                                   │
│  PROMPT         │  GENERATED CODE                   │
│  ┌───────────┐  │  ┌─────────────────────────────┐  │
│  │Parse user │  │  │def parse_user_id(input):   │  │
│  │IDs from   │  │  │    """                     │  │
│  │untrusted  │  │  │    Parse user ID from      │  │
│  │input...   │◄─┼──│    untrusted input.        │  │
│  │           │  │  │    ...                     │  │
│  │Return None│  │  │    """                     │  │
│  │on failure │  │  │    if not input:           │  │
│  │...        │  │  │        return None         │  │
│  │           │  │  │    cleaned = input.strip() │  │
│  │Handle     │  │  │    if not cleaned:         │  │
│  │unicode.   │  │  │        return None         │  │
│  └───────────┘  │  │    ...                     │  │
│   ◆ 15 lines    │  │    [continues 180+ more    │  │
│   ◆ Blue glow   │  │     lines...]              │  │
│                 │  │                             │  │
│                 │  └─────────────────────────────┘  │
│                 │   ○ ~200 lines                    │
│                 │   ○ No glow (just output)         │
│                 │                                   │
├─────────────────┴───────────────────────────────────┤
│  Ratio: "1:5 to 1:10"                              │
│  "A good prompt is a fifth to a tenth the size      │
│   of the code it generates."                        │
└─────────────────────────────────────────────────────┘
```

### Code Structure (Remotion)

```typescript
const PromptGovernsCode: React.FC = () => {
  const frame = useCurrentFrame();

  // Prompt animation
  const promptOpacity = interpolate(
    frame,
    [0, 60],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const promptGlow = 0.8 + Math.sin(frame * 0.1) * 0.2;

  // Code animation
  const codeOpacity = interpolate(
    frame,
    [90, 150],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Code scroll (shows extent)
  const codeScroll = interpolate(
    frame,
    [150, 240],
    [0, 100],
    { extrapolateRight: 'clamp' }
  );

  // Leverage indicator
  const leverageOpacity = interpolate(
    frame,
    [270, 320],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Left: Prompt */}
      <div style={{
        position: 'absolute',
        left: 100,
        top: 200,
        opacity: promptOpacity,
      }}>
        <PromptCard
          glowIntensity={promptGlow}
          lineCount={15}
        />
      </div>

      {/* Connection arrow */}
      <GovernsArrow
        opacity={Math.min(promptOpacity, codeOpacity)}
      />

      {/* Right: Code */}
      <div style={{
        position: 'absolute',
        right: 100,
        top: 150,
        opacity: codeOpacity,
      }}>
        <CodeFileCard
          scrollPosition={codeScroll}
          lineCount={200}
          showMinimap={true}
        />
      </div>

      {/* Ratio indicator */}
      <RatioIndicator
        ratio="1:5 to 1:10"
        opacity={leverageOpacity}
      />
    </AbsoluteFill>
  );
};
```

### Prompt Card Component

```typescript
const PromptCard: React.FC<{
  glowIntensity: number;
  lineCount: number;
}> = ({ glowIntensity, lineCount }) => {
  return (
    <div style={{
      width: 280,
      background: 'rgba(74, 144, 217, 0.1)',
      border: '2px solid #4A90D9',
      borderRadius: 12,
      padding: 20,
      boxShadow: `0 0 ${40 * glowIntensity}px rgba(74, 144, 217, ${0.5 * glowIntensity})`,
    }}>
      <div style={{
        fontSize: 14,
        color: '#4A90D9',
        fontFamily: 'JetBrains Mono',
        lineHeight: 1.6,
      }}>
        Parse user IDs from<br />
        untrusted input.<br />
        <br />
        Return None on failure,<br />
        never throw.<br />
        <br />
        Handle unicode.
      </div>
      <div style={{
        marginTop: 16,
        fontSize: 12,
        color: '#4A90D9',
        fontWeight: 'bold',
      }}>
        {lineCount} lines
      </div>
    </div>
  );
};
```

### Code File Card with Minimap

```typescript
const CodeFileCard: React.FC<{
  scrollPosition: number;
  lineCount: number;
  showMinimap: boolean;
}> = ({ scrollPosition, lineCount, showMinimap }) => {
  return (
    <div style={{
      width: 500,
      height: 500,
      background: '#1E1E2E',
      borderRadius: 8,
      overflow: 'hidden',
      position: 'relative',
    }}>
      {/* Scrolling code content */}
      <div style={{
        transform: `translateY(-${scrollPosition}px)`,
        padding: 16,
        fontSize: 11,
        fontFamily: 'JetBrains Mono',
        color: '#A0A0A0',
      }}>
        {generateCodeLines(lineCount)}
      </div>

      {/* Minimap showing full extent */}
      {showMinimap && (
        <div style={{
          position: 'absolute',
          right: 8,
          top: 8,
          width: 60,
          height: 480,
          background: '#2A2A3E',
          borderRadius: 4,
        }}>
          <MinimapContent lines={lineCount} />
          <MinimapViewport position={scrollPosition / lineCount} />
        </div>
      )}

      {/* Line count badge */}
      <div style={{
        position: 'absolute',
        bottom: 12,
        right: 80,
        fontSize: 12,
        color: '#666',
      }}>
        ~{lineCount} lines
      </div>
    </div>
  );
};
```

### Easing

- Prompt fade: `easeOutCubic`
- Prompt glow: `easeInOutSine` (pulsing)
- Code fade: `easeOutCubic`
- Code scroll: `easeInOutQuad`
- Leverage fade: `easeOutCubic`

## Narration Sync

> "A good prompt is a fifth to a tenth the size of the code it generates. You're specifying what and why, not how. And that compression matters."

The size comparison is fully visible during this narration. The "1:5 to 1:10" ratio appears as "a fifth to a tenth" is spoken.

## Audio Notes

- Soft hum for glowing prompt
- Scrolling sound for code file
- Emphasis sound for leverage reveal
- Prompt clearly has the "authority" sound

## Visual Style Notes

- Prompt GLOWS, code does not
- Size difference is stark and intentional
- Minimap shows code extent without needing to scroll everything
- This demonstrates leverage/efficiency
- The prompt is the source of truth

## Transition

Hard cut to Section 3.14 introducing Grounding Capital with the material properties panel.
