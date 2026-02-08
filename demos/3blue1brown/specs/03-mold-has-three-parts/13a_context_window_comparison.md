# Section 3.13a: Context Window Comparison -- Prompts vs Raw Code

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 14:15 - 14:35

## Visual Description

Two context windows side by side, identical in size. LEFT window: filled with 15,000 tokens of raw code -- dense, monospace, hard to parse, visually overwhelming. RIGHT window: filled with prompts for ten modules -- clean natural language, clear section headings, readable intent. Both windows are labeled with their token count and what they represent. The right window represents ten times more system knowledge despite being the same size. This is distinct from the Part 1 (Section 1.6) context window visualization, which showed a fixed window over a growing codebase. Here, the comparison is about information DENSITY -- what fits in the same window and how much knowledge it carries.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Side-by-side layout with clear separation

### Animation Elements

1. **Left Window: Raw Code**
   - Title: "15,000 tokens of code"
   - Container: Dark code background (#1E1E2E) with subtle border
   - Content: Dense monospace code filling the entire window
   - Syntax highlighting in muted grays and dulled colors
   - No clear structure visible -- wall of text
   - Scrollbar indicating more content
   - Label at bottom: "~1 module"
   - Overall feeling: cramped, hard to read, token-expensive

2. **Right Window: Prompts**
   - Title: "15,000 tokens of prompts"
   - Container: Same size, slight blue tint background (#1E1E2E with blue cast)
   - Content: Ten clearly labeled prompt sections
   - Natural language, readable at a glance
   - Each prompt section: module name header + brief spec text
   - Blue glow (#4A90D9) around section headers
   - Label at bottom: "~10 modules"
   - Overall feeling: organized, scannable, leveraging model strengths

3. **Window Frame (Shared)**
   - Both windows: identical size (e.g., 750x650px)
   - Glowing border representing context window capacity
   - Label above each: "Context Window (15K tokens)"
   - The identical framing is critical -- same capacity, different content

4. **Knowledge Multiplier**
   - Text appearing below/between the windows after both are shown
   - "Same tokens. 10x the system knowledge."
   - Or: "1 module vs 10 modules"
   - Arrows or visual indicator showing the leverage difference

5. **Natural Language Advantage Annotation**
   - Muted citation text: "Natural language comments improved generation quality by 41% (UC Berkeley, 2024)"
   - Positioned below the right window
   - Connects the visual to the research backing

### Animation Sequence

1. **Frame 0-90 (0-3s):** Left window builds
   - Window frame draws in
   - "Context Window (15K tokens)" label appears above
   - Code content floods in -- typing or scroll-fill effect
   - Dense, overwhelming, immediate visual impression of "too much"
   - Title: "15,000 tokens of code"

2. **Frame 90-120 (3-4s):** Left window labeled
   - "~1 module" label fades in at bottom
   - The viewer understands: all those tokens buy you ONE module of context
   - Brief hold

3. **Frame 120-240 (4-8s):** Right window builds
   - Window frame draws in (same size -- this is important)
   - "Context Window (15K tokens)" label appears above (identical)
   - Prompt content appears section by section
   - Ten module headers with natural language descriptions
   - Clean, readable, clearly organized
   - Title: "15,000 tokens of prompts"

4. **Frame 240-300 (8-10s):** Right window labeled
   - "~10 modules" label fades in at bottom
   - Blue glow (#4A90D9) on module headers
   - The contrast with the left window is stark

5. **Frame 300-390 (10-13s):** Knowledge multiplier
   - "Same tokens. 10x the system knowledge." fades in below both windows
   - Brief visual emphasis: the right window's border glows brighter
   - Optional: "10x" rendered large and bold between the windows

6. **Frame 390-480 (13-16s):** Research citation
   - "NL comments improved generation +41% (UC Berkeley, 2024)" fades in as muted text
   - Positioned below right window
   - "Author-defined context, not machine-assembled" text appears below left window
   - Connects to narration about leveraging model strengths

7. **Frame 480-600 (16-20s):** Hold for narration completion
   - Full composition visible
   - Right window gently pulses (this is the better approach)
   - Left window slightly dimmed (this is the problem)
   - Holds through narration about "author-defined, not machine-assembled"

### Visual Design: Context Window Comparison

```
+----------------------------------------------------------+
|                                                          |
| Context Window (15K tokens)  Context Window (15K tokens) |
| +------------------------+  +------------------------+   |
| | def parse_user_id(inp  |  | ## user_parser         |   |
| |   """Parse user ID fr  |  | Parse user IDs from    |   |
| |   if not input:        |  | untrusted input.       |   |
| |     return None        |  | Return None on failure.|   |
| |   cleaned = input.str  |  |                        |   |
| |   if not cleaned:      |  | ## auth_handler        |   |
| |     return None        |  | Handle OAuth2 tokens.  |   |
| |   try:                 |  | Validate, refresh,     |   |
| |     uid = int(cleaned) |  | cache results.         |   |
| |   except ValueError:   |  |                        |   |
| |     return None        |  | ## data_pipeline       |   |
| |   if uid < 0:          |  | ETL from Postgres to   |   |
| |     return None        |  | Elasticsearch. Handle  |   |
| |   if uid > MAX_UID:    |  | schema drift.          |   |
| |     return None        |  |                        |   |
| |   ...                  |  | ## payment_processor   |   |
| |   ...                  |  | Stripe integration.    |   |
| |   ...                  |  | Idempotent charges.    |   |
| |   (dense code cont.)   |  |                        |   |
| |   ████████████████████ |  | ## email_service ...   |   |
| |   ████████████████████ |  | ## cache_layer ...     |   |
| |   ████████████████████ |  | ## api_gateway ...     |   |
| +------------------------+  | ## search_index ...    |   |
| ~1 module                   | ## notification ...    |   |
|                             | ## audit_logger ...    |   |
|                             +------------------------+   |
|                             ~10 modules                  |
|                                                          |
|       Same tokens. 10x the system knowledge.             |
|                                                          |
+----------------------------------------------------------+
  Left: gray, dense             Right: blue glow, readable
  Token-expensive code          Token-efficient prompts
```

### Code Structure (Remotion)

```typescript
const ContextWindowComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Left window build
  const leftFrameOpacity = interpolate(
    frame, [0, 30], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const leftContentFill = interpolate(
    frame, [15, 90], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const leftLabelOpacity = interpolate(
    frame, [90, 120], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Right window build
  const rightFrameOpacity = interpolate(
    frame, [120, 150], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const rightContentFill = interpolate(
    frame, [150, 240], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const rightLabelOpacity = interpolate(
    frame, [240, 270], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Knowledge multiplier
  const multiplierOpacity = interpolate(
    frame, [300, 360], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Research citation
  const citationOpacity = interpolate(
    frame, [390, 440], [0, 0.7],
    { extrapolateRight: 'clamp' }
  );

  // Right window emphasis pulse
  const rightPulse = frame > 300
    ? 1.0 + Math.sin((frame - 300) * 0.07) * 0.08
    : 1.0;

  // Left window dim
  const leftDim = frame > 300
    ? interpolate(frame, [300, 390], [1, 0.6], { extrapolateRight: 'clamp' })
    : 1.0;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <div style={{
        display: 'flex',
        justifyContent: 'center',
        gap: 60,
        marginTop: 60,
      }}>
        {/* Left: Raw Code Window */}
        <div style={{ opacity: leftFrameOpacity * leftDim }}>
          <WindowTitle text="Context Window (15K tokens)" />
          <CodeWindow
            fillProgress={leftContentFill}
            content={denseCodeContent}
            width={750}
            height={650}
          />
          <WindowLabel
            text="~1 module"
            opacity={leftLabelOpacity}
            color="#888"
          />
        </div>

        {/* Right: Prompts Window */}
        <div style={{
          opacity: rightFrameOpacity,
          transform: `scale(${rightPulse})`,
        }}>
          <WindowTitle text="Context Window (15K tokens)" />
          <PromptWindow
            fillProgress={rightContentFill}
            modules={tenModulePrompts}
            width={750}
            height={650}
            glowColor="#4A90D9"
          />
          <WindowLabel
            text="~10 modules"
            opacity={rightLabelOpacity}
            color="#4A90D9"
          />
        </div>
      </div>

      {/* Knowledge multiplier */}
      <div style={{
        position: 'absolute',
        bottom: 140,
        width: '100%',
        textAlign: 'center',
        opacity: multiplierOpacity,
      }}>
        <span style={{
          fontSize: 32,
          fontWeight: 700,
          color: '#FFFFFF',
          fontFamily: 'Inter, sans-serif',
        }}>
          Same tokens.{' '}
          <span style={{ color: '#4A90D9', fontSize: 38 }}>10x</span>
          {' '}the system knowledge.
        </span>
      </div>

      {/* Research citation */}
      <div style={{
        position: 'absolute',
        bottom: 80,
        width: '100%',
        textAlign: 'center',
        opacity: citationOpacity,
      }}>
        <span style={{
          fontSize: 18,
          color: '#B0B0C0',
          fontFamily: 'Inter, sans-serif',
        }}>
          NL comments improved generation +41% (UC Berkeley, 2024)
          {'  |  '}
          Author-defined context, not machine-assembled
        </span>
      </div>
    </AbsoluteFill>
  );
};
```

### Code Window Component

```typescript
const CodeWindow: React.FC<{
  fillProgress: number;
  content: string[];
  width: number;
  height: number;
}> = ({ fillProgress, content, width, height }) => {
  const visibleLines = Math.floor(content.length * fillProgress);

  return (
    <div style={{
      width,
      height,
      backgroundColor: '#1E1E2E',
      borderRadius: 8,
      border: '1px solid #333',
      overflow: 'hidden',
      padding: 16,
      position: 'relative',
    }}>
      <div style={{
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: 11,
        lineHeight: 1.5,
        color: '#A0A0A0',
      }}>
        {content.slice(0, visibleLines).map((line, i) => (
          <div key={i} style={{ whiteSpace: 'pre' }}>
            <span style={{ color: '#555', marginRight: 12 }}>
              {String(i + 1).padStart(3)}
            </span>
            {line}
          </div>
        ))}
      </div>
      {/* Scrollbar indicator */}
      <div style={{
        position: 'absolute',
        right: 4,
        top: 4,
        width: 6,
        height: 60,
        backgroundColor: '#444',
        borderRadius: 3,
      }} />
    </div>
  );
};
```

### Prompt Window Component

```typescript
const PromptWindow: React.FC<{
  fillProgress: number;
  modules: Array<{ name: string; description: string }>;
  width: number;
  height: number;
  glowColor: string;
}> = ({ fillProgress, modules, width, height, glowColor }) => {
  const visibleModules = Math.floor(modules.length * fillProgress);

  return (
    <div style={{
      width,
      height,
      backgroundColor: 'rgba(30, 30, 46, 0.95)',
      borderRadius: 8,
      border: `1px solid ${glowColor}40`,
      overflow: 'hidden',
      padding: 16,
      boxShadow: `0 0 20px ${glowColor}15`,
    }}>
      {modules.slice(0, visibleModules).map((mod, i) => (
        <div key={i} style={{ marginBottom: 12 }}>
          <div style={{
            fontSize: 15,
            fontWeight: 600,
            color: glowColor,
            fontFamily: 'Inter, sans-serif',
            marginBottom: 2,
          }}>
            ## {mod.name}
          </div>
          <div style={{
            fontSize: 13,
            color: '#C0C0D0',
            fontFamily: 'Inter, sans-serif',
            lineHeight: 1.4,
          }}>
            {mod.description}
          </div>
        </div>
      ))}
    </div>
  );
};
```

### Sample Module Prompts (Data)

```typescript
const tenModulePrompts = [
  { name: 'user_parser', description: 'Parse user IDs from untrusted input. Return None on failure.' },
  { name: 'auth_handler', description: 'Handle OAuth2 tokens. Validate, refresh, cache results.' },
  { name: 'data_pipeline', description: 'ETL from Postgres to Elasticsearch. Handle schema drift.' },
  { name: 'payment_processor', description: 'Stripe integration. Idempotent charges. Webhook verify.' },
  { name: 'email_service', description: 'Transactional email via SendGrid. Template rendering.' },
  { name: 'cache_layer', description: 'Redis caching with TTL. Graceful fallback on miss.' },
  { name: 'api_gateway', description: 'Rate limiting, auth middleware, request validation.' },
  { name: 'search_index', description: 'Full-text search over documents. Relevance tuning.' },
  { name: 'notification_hub', description: 'Push, SMS, email routing. User preference respect.' },
  { name: 'audit_logger', description: 'Immutable audit trail. Structured events. Compliance.' },
];
```

### Easing

- Window frame draws: `easeOutCubic`
- Code flood-fill: `easeInOutQuad` (accelerating fill)
- Prompt section appearances: `easeOutCubic` (staggered per module)
- Labels: `easeOutCubic`
- Knowledge multiplier: `easeOutBack` (slight overshoot for emphasis)
- Right window pulse: Sinusoidal (manual Math.sin)
- Left window dim: `easeInQuad`
- Citation: `easeOutCubic`

## Narration Sync

> "Remember the context window problem? Code is token-expensive. But prompts are natural language -- and these models were trained on up to thirty times more natural language than code. Researchers found that just adding natural language comments to code training data improved generation quality by forty-one percent. The prompt isn't fighting the model's strengths. It's leveraging them."

> "And unlike agentic tools that dynamically guess which code to load into context -- and increasingly guess wrong -- each prompt declares its own dependencies. The context is author-defined, not machine-assembled."

- "Remember the context window problem?" -- Left window (code) building, immediate density
- "Code is token-expensive" -- Left window fully loaded, "~1 module" label appears
- "But prompts are natural language" -- Right window begins building, clean and readable
- "thirty times more natural language than code" -- Right window filling with ten modules
- "improved generation quality by forty-one percent" -- Citation text appears
- "leveraging them" -- "Same tokens. 10x the system knowledge." fades in
- "author-defined, not machine-assembled" -- Full composition held, right window pulsing

## Audio Notes

- Left window code fill: rapid typing/scrolling sound -- overwhelming, chaotic
- Right window prompt fill: cleaner, measured appearance sounds -- organized
- "10x" reveal: satisfying emphasis tone
- Contrast: left side feels noisy, right side feels clean
- Citation appearance: soft, unobtrusive

## Visual Style Notes

- This comparison is about DENSITY AND READABILITY, not about window size (that was Part 1 Section 1.6)
- The left window should feel overwhelming -- a wall of dense code that is hard to parse
- The right window should feel effortless -- you can skim it and immediately understand ten modules
- The identical window sizes are critical -- same capacity, radically different information density
- "10x" is rendered larger and in blue (#4A90D9) to emphasize the multiplier
- Module headers in the right window use blue glow to connect to the prompt visual language
- The dim on the left window after the comparison is established subtly signals "this is the inferior approach"
- Research citations stay muted -- supporting evidence, not the main visual
- This spec is complementary to but distinct from 01-economics/06_context_rot.md, which showed the context window as a fixed aperture over a growing codebase; this one shows what you can FIT in that same aperture

## Transition

Continues into narration about "modules around 250 lines have the lowest defect density" leading to Section 3.14 (grounding panel). The context window comparison fades as the mold visualization returns.
