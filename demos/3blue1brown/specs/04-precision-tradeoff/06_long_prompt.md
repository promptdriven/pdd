# Section 4.6: Long Prompt Display

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 15:00 - 15:15

## Visual Description

A dense, 50-line prompt file (`parser_v1.prompt`) appears on screen. The prompt is detailed, specifying edge cases, error handling, and exact behaviors. Only 2-3 test walls appear nearby, emphasizing that without tests, the prompt must carry all the precision burden.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Code display centered, walls on right

### Animation Elements

1. **Prompt File Display**
   - File: `parser_v1.prompt`
   - ~50 lines of detailed requirements
   - Blue (#4A90D9) header/accent
   - Syntax-highlighted content

2. **Content Scroll** (optional)
   - Slow auto-scroll to show density
   - Or show condensed view with line count

3. **Test Walls (Few)**
   - Only 2-3 amber walls on right side
   - Small, sparse arrangement
   - Emphasizes lack of test coverage

4. **Line Count Indicator**
   - "50 lines" badge visible
   - Emphasizes prompt complexity

### Visual Design

```
┌────────────────────────────────────┐
│                                    │
│  ┌─ parser_v1.prompt ────────────┐ │
│  │                               │ │
│  │ # User ID Parser - v1         │ │
│  │ ## Requirements               │ │    ┌──┐
│  │ - Parse user IDs from input   │ │    │  │ ← Only 2-3
│  │ - Handle null: return None    │ │    └──┘   test walls
│  │ - Handle empty: return None   │ │    ┌──┐
│  │ - Handle whitespace-only...   │ │    │  │
│  │ - Support unicode characters  │ │    └──┘
│  │ - Trim leading/trailing...    │ │
│  │ - Validate format: alphan...  │ │
│  │ - Max length: 64 characters   │ │
│  │ - Min length: 1 character     │ │
│  │ - ... (more lines)            │ │
│  │                        [50L]  │ │
│  └───────────────────────────────┘ │
│                                    │
└────────────────────────────────────┘
```

### Sample Prompt Content

```markdown
# User ID Parser - Version 1

## Purpose
Parse and validate user IDs from untrusted input sources.

## Input Handling
- Accept string input from any source
- Handle null/undefined gracefully
- Handle empty strings
- Handle whitespace-only strings
- Trim leading and trailing whitespace

## Validation Rules
- Must be alphanumeric plus underscore and hyphen
- Minimum length: 1 character
- Maximum length: 64 characters
- Case-insensitive comparison
- No leading or trailing hyphens
- No consecutive underscores

## Unicode Support
- Accept Unicode letters in addition to ASCII
- Normalize to NFC form before processing
- Handle combining characters correctly

## Error Handling
- Never throw exceptions
- Return None for invalid input
- Log validation failures for debugging
- Provide error context in logs

## Edge Cases
- Single character IDs are valid
- Numeric-only IDs are valid
- IDs starting with numbers are valid
- Empty after trimming → None
- Only special chars → None

## Performance
- O(n) complexity maximum
- No regex compilation per call
- Cache validation patterns

## Return Value
- Valid: cleaned string
- Invalid: None (never raise)

## Logging
- Debug: all inputs
- Warning: validation failures
- Error: never (no exceptions)
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Prompt file appears
   - File container fades in
   - Header visible: `parser_v1.prompt`
   - Initial content visible

2. **Frame 90-270 (3-9s):** Content reveals
   - Slow scroll or expand to show density
   - Line count becomes visible
   - Emphasis on how much is specified

3. **Frame 270-360 (9-12s):** Test walls appear
   - Only 2-3 amber walls fade in
   - Positioned to the right
   - Small, sparse - not much coverage

4. **Frame 360-450 (12-15s):** Hold
   - Full prompt visible with line count
   - Few walls visible
   - Contrast established

### Code Structure (Remotion)

```typescript
const LongPrompt: React.FC = () => {
  const frame = useCurrentFrame();

  // Container opacity
  const containerOpacity = interpolate(
    frame,
    [0, 90],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Scroll progress (shows density)
  const scrollProgress = interpolate(
    frame,
    [90, 270],
    [0, 0.6],
    { extrapolateRight: 'clamp' }
  );

  // Test walls opacity
  const wallsOpacity = interpolate(
    frame,
    [270, 330],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Prompt file display */}
      <PromptFile
        filename="parser_v1.prompt"
        content={longPromptContent}
        lineCount={50}
        opacity={containerOpacity}
        scrollProgress={scrollProgress}
      />

      {/* Few test walls */}
      <TestWallsSmall
        count={3}
        opacity={wallsOpacity}
        position={{ x: 1400, y: 350 }}
      />

      {/* Line count badge */}
      <LineCountBadge
        count={50}
        opacity={containerOpacity}
      />
    </AbsoluteFill>
  );
};
```

### Prompt File Component

```typescript
const PromptFile: React.FC<{
  filename: string;
  content: string;
  lineCount: number;
  opacity: number;
  scrollProgress: number;
}> = ({ filename, content, lineCount, opacity, scrollProgress }) => {
  const lines = content.split('\n');
  const visibleStart = Math.floor(scrollProgress * (lines.length - 20));
  const visibleLines = lines.slice(visibleStart, visibleStart + 25);

  return (
    <div style={{
      position: 'absolute',
      left: 150,
      top: 100,
      width: 1100,
      height: 800,
      opacity,
    }}>
      {/* File header */}
      <div style={{
        backgroundColor: '#4A90D9',
        padding: '12px 20px',
        borderTopLeftRadius: 8,
        borderTopRightRadius: 8,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'space-between',
      }}>
        <span style={{
          color: 'white',
          fontFamily: 'monospace',
          fontSize: 18,
        }}>
          {filename}
        </span>
        <span style={{
          color: 'rgba(255, 255, 255, 0.7)',
          fontSize: 14,
        }}>
          {lineCount} lines
        </span>
      </div>

      {/* File content */}
      <div style={{
        backgroundColor: '#1E1E2E',
        padding: 20,
        borderBottomLeftRadius: 8,
        borderBottomRightRadius: 8,
        height: 700,
        overflow: 'hidden',
      }}>
        {visibleLines.map((line, i) => (
          <div key={i} style={{
            fontFamily: 'monospace',
            fontSize: 14,
            color: line.startsWith('#') ? '#4A90D9' :
                   line.startsWith('-') ? '#D9944A' :
                   'rgba(255, 255, 255, 0.8)',
            marginBottom: 4,
            whiteSpace: 'pre',
          }}>
            {line}
          </div>
        ))}

        {/* Fade indicator at bottom */}
        <div style={{
          position: 'absolute',
          bottom: 0,
          left: 0,
          right: 0,
          height: 80,
          background: 'linear-gradient(transparent, #1E1E2E)',
        }} />
      </div>
    </div>
  );
};
```

### Test Walls Small Component

```typescript
const TestWallsSmall: React.FC<{
  count: number;
  opacity: number;
  position: { x: number; y: number };
}> = ({ count, opacity, position }) => {
  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      opacity,
    }}>
      {[...Array(count)].map((_, i) => (
        <div key={i} style={{
          width: 40,
          height: 60,
          backgroundColor: '#D9944A',
          borderRadius: 4,
          marginBottom: 20,
          boxShadow: '0 0 20px rgba(217, 148, 74, 0.4)',
        }} />
      ))}

      {/* Label */}
      <div style={{
        marginTop: 10,
        color: 'rgba(255, 255, 255, 0.5)',
        fontSize: 14,
        textAlign: 'center',
      }}>
        3 tests
      </div>
    </div>
  );
};
```

### Easing

- Container fade-in: `easeOutCubic`
- Scroll: `easeInOutQuad` (smooth reading pace)
- Walls fade-in: `easeOutCubic`

## Narration Sync

> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."

The dense prompt is visible as the narration describes all the things that must be specified.

## Audio Notes

- Soft "paper" sound as prompt appears
- Subtle scroll sound during content reveal
- Quiet, contemplative atmosphere

## Visual Style Notes

- Prompt should look dense and detailed
- Syntax highlighting adds visual interest
- Few walls emphasize lack of coverage
- The contrast sets up the next scene

## Transition

Cuts to Section 4.7 showing the short prompt with many tests.
