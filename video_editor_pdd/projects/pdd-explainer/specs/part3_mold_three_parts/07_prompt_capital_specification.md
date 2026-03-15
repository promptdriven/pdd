[Remotion]

# Section 3.7: Prompt Capital — The Specification

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 14:27 - 14:47

## Visual Description
The injection nozzle of the mold highlights as the narrator introduces prompt capital. Text representing the prompt specification flows into the mold like injection material: "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." A file label `user_parser.prompt` is briefly visible. Then the same prompt generates code twice — two different implementations appear side by side, with different variable names and slightly different structure, but both pass all tests. The ratio "1:5 to 1:10" appears, showing the compression advantage. Finally, two context windows are compared: LEFT filled with 15,000 tokens of dense code, RIGHT filled with clean prompts for ten modules — same window size, ten times more system knowledge.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Nozzle Region:** Top-center, funnel shape 100px wide at top → 40px at bottom, `#4A90D9` at 0.5 opacity with 4px glow blur
- **Prompt Text Flow:** Text strings flow downward from nozzle into the mold cavity, styled as glowing blue text particles:
  - "Parse user IDs from untrusted input" — `#4A90D9`, 16px
  - "Return None on failure, never throw" — `#4A90D9`, 16px
  - "Handle unicode" — `#4A90D9`, 16px
- **File Label:** `user_parser.prompt` — JetBrains Mono, 14px, `#94A3B8`, positioned above nozzle with a document icon
- **Dual Generation Panel:** Two code blocks side by side, each 500px wide x 280px tall, 60px gap
  - Left block: Code-line texture pattern A (class-based style), border `rgba(74,144,217,0.3)`, green checkmark below
  - Right block: Code-line texture pattern B (function-based style), border `rgba(74,144,217,0.3)`, green checkmark below
  - Connecting line from same prompt document to both blocks
  - Label between checkmarks: "Different code. Same behavior." — `#FFFFFF`, 18px
- **Compression Ratio:** Large text "1:5 to 1:10" — `#4A90D9`, 48px bold, with explanatory label: "Prompt-to-code compression" — `#94A3B8`, 16px
  - Visual: Small glowing prompt document (left, ~50px tall) connected by expanding arrow to larger code block (right, ~300px tall)
- **Context Window Comparison (final beat):**
  - Two side-by-side rectangles, each 600px wide x 350px tall, labeled "Context Window"
  - LEFT: Packed with dense horizontal lines (code), `rgba(239,68,68,0.15)` red tint on ~30% of lines (irrelevant code), tiny green highlights on ~5% (relevant). Label: "15,000 tokens of code" — `#94A3B8`, 14px. Overall: cluttered, noisy
  - RIGHT: Clean horizontal lines (prompts), all `rgba(74,144,217,0.2)` blue tint, well-spaced. Label: "Prompts for 10 modules" — `#94A3B8`, 14px. Sub-label: "10× more system knowledge" — `#4A90D9`, 16px. Overall: spacious, focused

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Nozzle region highlights with blue glow. `user_parser.prompt` file label fades in above
2. **Frame 40-120 (1.33-4.0s):** Prompt text strings flow downward through nozzle one by one (20-frame stagger), each drifting down with particle trail effect. They enter the mold cavity
3. **Frame 120-220 (4.0-7.33s):** Dual generation — prompt document at top-center, two connecting lines draw to left and right code blocks. Both blocks fill with code-line textures simultaneously but visibly different patterns. Green checkmarks appear below both
4. **Frame 220-270 (7.33-9.0s):** "Different code. Same behavior." text fades in centered between the two blocks
5. **Frame 270-360 (9.0-12.0s):** Scene transitions (cross-fade). Compression ratio visualization: small prompt document on left, expanding arrow, large code block on right. "1:5 to 1:10" scales in with emphasis
6. **Frame 360-520 (12.0-17.33s):** Scene transitions to context window comparison. Both windows draw in simultaneously. LEFT fills with dense noisy code lines (red highlights scattered). RIGHT fills with clean spaced prompt lines (blue tint). Labels appear. The contrast is stark
7. **Frame 520-600 (17.33-20.0s):** Hold. "10× more system knowledge" pulses once on right window. Text appears below: "Every token is author-curated." — `#FFFFFF`, 18px

### Typography
- File Label: JetBrains Mono, 14px, regular (400), `#94A3B8`
- Prompt Text: Inter, 16px, regular (400), `#4A90D9`
- "Different code. Same behavior.": Inter, 18px, semi-bold (600), `#FFFFFF`
- Compression Ratio: Inter, 48px, bold (800), `#4A90D9`
- Compression Label: Inter, 16px, regular (400), `#94A3B8`
- Context Window Labels: Inter, 14px, regular (400), `#94A3B8`
- "10× more system knowledge": Inter, 16px, bold (700), `#4A90D9`
- Emphasis Text: Inter, 18px, semi-bold (600), `#FFFFFF`

### Easing
- Nozzle highlight: `easeInOut(sine)`
- Prompt text flow: `easeIn(quad)` for downward drift
- Code block fill: `easeOut(cubic)`
- Checkmark pop: `easeOut(back(1.3))`
- Compression ratio scale: `easeOut(back(1.5))`
- Context window draw: `easeOut(cubic)`
- Code line fill (LEFT): `linear` (constant stream, overwhelming)
- Prompt line fill (RIGHT): `easeOut(quad)` (clean, deliberate)

## Narration Sync
> "Second: the prompt. Your specification of what you want."
> "The prompt doesn't define the walls — tests do that. The prompt defines what you're asking for and why."
> "Notice something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."
> "A good prompt is a fifth to a tenth the size of the code it generates."
> "This is why the context window advantage we talked about is so powerful. You're not stuffing code into a window and hoping the model figures it out. You're giving it natural language — its strongest modality — in a window that's five to ten times more spacious."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Nozzle Highlight */}
  <Sequence from={0} durationInFrames={40}>
    <NozzleHighlight color="#4A90D9" />
    <FileLabel text="user_parser.prompt" />
  </Sequence>

  {/* Prompt Text Flow */}
  <Sequence from={40} durationInFrames={80}>
    <PromptTextFlow
      lines={[
        "Parse user IDs from untrusted input",
        "Return None on failure, never throw",
        "Handle unicode"
      ]}
      stagger={20}
    />
  </Sequence>

  {/* Dual Generation */}
  <Sequence from={120} durationInFrames={100}>
    <DualGeneration
      promptSource="user_parser.prompt"
      leftStyle="class-based"
      rightStyle="functional"
    />
  </Sequence>

  {/* Same Behavior Label */}
  <Sequence from={220} durationInFrames={50}>
    <CenterLabel text="Different code. Same behavior." />
  </Sequence>

  {/* Compression Ratio */}
  <Sequence from={270} durationInFrames={90}>
    <CompressionRatio ratio="1:5 to 1:10" />
  </Sequence>

  {/* Context Window Comparison */}
  <Sequence from={360} durationInFrames={160}>
    <ContextWindowComparison
      leftLabel="15,000 tokens of code"
      rightLabel="Prompts for 10 modules"
      rightSubLabel="10× more system knowledge"
    />
  </Sequence>

  {/* Final Emphasis */}
  <Sequence from={520} durationInFrames={80}>
    <EmphasisText text="Every token is author-curated." y={800} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "promptFile": "user_parser.prompt",
  "promptLines": [
    "Parse user IDs from untrusted input",
    "Return None on failure, never throw",
    "Handle unicode"
  ],
  "compressionRatio": {
    "min": "1:5",
    "max": "1:10",
    "displayText": "1:5 to 1:10",
    "color": "#4A90D9"
  },
  "contextComparison": {
    "left": {
      "label": "15,000 tokens of code",
      "tokenCount": 15000,
      "irrelevantPct": 0.30,
      "relevantPct": 0.05,
      "tint": "rgba(239,68,68,0.15)"
    },
    "right": {
      "label": "Prompts for 10 modules",
      "moduleCount": 10,
      "multiplier": "10×",
      "tint": "rgba(74,144,217,0.2)"
    }
  }
}
```

---
