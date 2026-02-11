# Audio-Synced Animation Process

How to make a Remotion animation match a narration script so the visuals respond to the words as they're spoken.

## Overview

The pipeline takes a narration script, renders it to audio, transcribes it with word-level timestamps, then uses those timestamps to drive animation timing in Remotion. The result is a video where every visual event (a line drawing, a label appearing, a highlight effect) is keyed to the exact moment the narrator says the corresponding words.

```
tts_script.md → TTS segments → concatenated audio → Whisper timestamps → BEATS constants → Remotion component → rendered video
```

## Step 1: Identify the narration for the target section

Each Remotion composition corresponds to a section of the video. Find the matching narration in `narrative/tts_script.md`.

For the CodeCostChart composition (05), the relevant narration is in **Part 1: The Economics of Darning**, starting from "Now look at code." through "the debt ate the gains."

The TTS script is divided into sections separated by `---`. The `render_tts.py` parser splits on `---` and drops the first two parts (header + annotation key), so segment numbering starts at Part 1. Each paragraph within a section becomes one TTS segment file (`segment_000.wav`, `segment_001.wav`, etc.).

For CodeCostChart, the relevant segments are **003 through 009** (the "code economics" subsection within Part 1).

## Step 2: Render TTS audio segments

Use the existing TTS pipeline to generate audio for each segment:

```bash
cd tools/tts
python render_tts.py ../../narrative/tts_script.md ../../outputs/tts/
```

This produces `outputs/tts/segment_NNN.wav` files. Each file is one spoken paragraph.

If segments already exist, skip this step.

## Step 3: Concatenate segments with pauses

The TTS script specifies pauses between segments (`[PAUSE: 1.5s]`). Concatenate the relevant segment files with silence gaps matching those pauses.

```bash
mkdir -p outputs/tts/mini_test
cd outputs/tts/mini_test

# Generate silence files for each inter-segment pause
ffmpeg -f lavfi -i anullsrc=r=24000:cl=mono -t 1.0 -q:a 9 -ac 1 silence_0.wav   # 1.0s
ffmpeg -f lavfi -i anullsrc=r=24000:cl=mono -t 1.5 -q:a 9 -ac 1 silence_1.wav   # 1.5s
# ... one per pause

# Create concat list
cat > concat_list.txt << 'EOF'
file '../../../outputs/tts/segment_003.wav'
file 'silence_0.wav'
file '../../../outputs/tts/segment_004.wav'
file 'silence_1.wav'
...
EOF

# Concatenate
ffmpeg -f concat -safe 0 -i concat_list.txt -c copy codecostchart_narration.wav
```

The pause durations come from the `[PAUSE: Xs]` annotations in the TTS script between the target segments.

**Key detail:** Match the sample rate of silence files to the TTS output (24000 Hz mono for Qwen3-TTS).

Copy the final concatenated audio to the Remotion public directory:

```bash
cp outputs/tts/mini_test/codecostchart_narration.wav remotion/public/
```

## Step 4: Transcribe with word-level timestamps

Run `faster-whisper` on the concatenated audio to get per-word timing:

```python
from faster_whisper import WhisperModel

model = WhisperModel("base", compute_type="int8")
segments, info = model.transcribe(
    "outputs/tts/mini_test/codecostchart_narration.wav",
    word_timestamps=True
)

words = []
segs = []
for seg in segments:
    segs.append({"start": seg.start, "end": seg.end, "text": seg.text.strip()})
    for w in seg.words:
        words.append({
            "word": w.word.strip(),
            "start": round(w.start, 2),
            "end": round(w.end, 2),
            "probability": round(w.probability, 3),
        })

import json
with open("outputs/tts/mini_test/word_timestamps.json", "w") as f:
    json.dump({"words": words, "segments": segs}, f, indent=2)
```

The output is a JSON file with two arrays:
- `words`: every word with `start`, `end`, `probability`
- `segments`: sentence-level groups with `start`, `end`, `text`

**Key detail:** The `base` model is fast but occasionally splits compound words ("co-pilot" → "co", "-pilot"). Use `medium` or `large-v2` for higher accuracy if needed.

## Step 5: Map narration cues to animation events

This is the creative step. Read through the narration and decide: **what should the viewer see when they hear each phrase?**

Write this out as a narration-to-animation map before writing any code.

### Principles

1. **A visual element should appear when the narrator talks about it, not before.** If the narrator says "But watch the dashed line" at 39s, the dashed line should not be visible before 39s.

2. **Label lines immediately.** When a line starts drawing, show its label right away so the viewer knows what they're looking at. Don't wait until the line finishes.

3. **Match the narrative arc.** The script has a rhetorical structure (setup → reveal → data). The animation should mirror it. Don't front-load visual complexity.

4. **Every narration phrase should have a visual response.** If the narrator says "barely moving," the chart should visually emphasize that the line is flat. If they say "Technical debt," highlight the debt area.

5. **Phrases that don't appear in the narration shouldn't appear visually.** If you have an annotation like "Same tools. Different codebase sizes." but the narrator never says it, don't show it.

### Example: CodeCostChart mapping

| Time | Narrator says | Visual event |
|------|--------------|-------------|
| 0.00s | "Now look at code." | Title + axes fade in |
| 1.94s | "For fifty years, generating new code was expensive." | Blue "Cost to Generate" line starts drawing with label |
| 5.44s | "Writing from scratch took hours, days, weeks." | Blue line still drawing (same sentence topic) |
| 8.44s | "weeks." | Blue line reaches 2020 |
| 9.00s | "So when something broke, you patched." | Amber "Patch Cost" line starts drawing with label |
| 13.12s | "It was rational." | Amber reaches 2020. Phase 1 complete. |
| 14.80s | "Now here's where it gets interesting." | Pause. Transition beat. |
| 17.50s | "AI made patching faster too." | Phase 2: blue plunges, amber forks into Small/Large CB |
| 31.26s | "each patch is getting faster" | Highlight the dropping small-codebase line |
| 37.66s | "these tools." | Phase 2 drawing complete |
| 39.24s | "But watch the dashed line" | **REVEAL:** dashed "True Cost" line draws for the first time. Other lines dim. |
| 43.52s | "barely moving." | Dashed line fully visible. Text overlay. |
| 47.10s | "every patch still leaves residue" | Debt area pulses |
| 49.36s | "Technical debt" | Pulse intensifies. "Technical debt accumulates" overlay. |
| 56.52s | "AI gave you a 60% speed up" | Data annotation card appears |
| 64.88s | "the debt ate the rest" | Crossing point annotation |

### Mistakes we caught in review

**Wrong:** The amber "Patch Cost" line started drawing at 5.44s ("Writing from scratch took hours"). But that sentence is about the cost to *generate* code (the blue line's topic). The amber line should start at 9.0s ("So when something broke, you patched") — the first time patching is mentioned.

**Wrong:** The dashed "total cost" line was drawn in Phase 1 (9s) and Phase 2 (17.5s), but the narrator doesn't mention it until 39.24s ("But watch the dashed line"). For 30 seconds, there was an unexplained line on screen. Removing it until the reveal created a much stronger narrative moment.

**Wrong:** Labels only appeared after a line finished drawing. You'd watch a line draw for 7 seconds with no idea what it represented. Labels should appear immediately with the line and track the drawing tip.

## Step 6: Encode beats as frame constants

Convert the timestamp map into a TypeScript constants file. Use a `s2f()` helper to convert seconds to frames at the target FPS.

```typescript
const MINI_FPS = 30;
const s2f = (seconds: number) => Math.round(seconds * MINI_FPS);

export const BEATS = {
  BLUE_LINE_START: s2f(1.94),   // 58  - "For fifty years"
  BLUE_LINE_END: s2f(8.44),     // 253 - "weeks."
  AMBER_LINE_START: s2f(9.0),   // 270 - "you patched"
  AMBER_LINE_END: s2f(13.12),   // 394 - "rational."
  // ...
};
```

**Key detail:** Always include the narration cue as a comment next to each beat. This makes the mapping auditable — you can read the constants file and immediately see whether the timing makes narrative sense.

The beat values flow from `word_timestamps.json`. Look up the word's `start` time and convert to frames.

## Step 7: Build the Remotion component

The component uses `useCurrentFrame()` and `interpolate()` to drive all animations from the BEATS constants.

Key patterns:

### Animated lines with tip-tracking labels

```tsx
// Label tracks the drawing tip (visible from start, not just at end)
const labelX = progress >= 1 ? endPt.x : tipX;
const labelY = progress >= 1 ? endPt.y : tipY;
const labelOp = interpolate(frame, [startFrame, startFrame + 20], [0, 1], {
  extrapolateLeft: "clamp", extrapolateRight: "clamp",
});
```

### Delayed reveal (element only appears when narrator mentions it)

```tsx
// Dashed line doesn't exist until narrator says "watch the dashed line"
<AnimatedLine
  data={fullDataset}
  startFrame={BEATS.REVEAL_DASHED_START}  // 39.24s
  endFrame={BEATS.REVEAL_DASHED_END}      // 43.52s
  dashed
/>
```

### Dimming other elements to focus attention

```tsx
const nonDashedOpacity = frame >= BEATS.REVEAL_DASHED_START
  ? interpolate(frame, [BEATS.REVEAL_DASHED_START, BEATS.REVEAL_DASHED_START + 30], [1, 0.25], clamp)
  : 1;

<AnimatedLine lineOpacity={nonDashedOpacity} ... />
```

### Pulse effects synced to emphasis words

```tsx
const debtPulse = frame >= BEATS.DEBT_HIGHLIGHT_START && frame <= BEATS.DEBT_HIGHLIGHT_END
  ? 0.6 + 0.4 * Math.sin(((frame - BEATS.DEBT_HIGHLIGHT_START) / 30) * Math.PI * 2 * 0.5)
  : 0;
```

### Audio playback

```tsx
<Audio src={staticFile("codecostchart_narration.wav")} />
```

The audio file must be in `remotion/public/`. Remotion's `<Audio>` component handles playback synced to the frame timeline.

## Step 8: Render and review

```bash
cd remotion
npx remotion render CodeCostChartMini --output ../outputs/mini_test/codecostchart_mini.mp4 --codec h264
```

**Review process:** Watch the video and check every narration cue against its visual event:

1. Does each line/element appear when the narrator first mentions it?
2. Can you identify what each line represents the moment it appears?
3. Do visual emphasis effects (dim, glow, pulse) match the narrator's emphasis words?
4. Are there any visual elements on screen that the narrator hasn't explained yet?

If any of these fail, go back to Step 5 and revise the mapping.

## Step 9: Iterate

This process typically takes 2-3 passes:

**Pass 1:** Get the basic structure right — which segments to use, rough beat mapping, component skeleton. The first render will have obvious mismatches.

**Pass 2:** Fix sequencing — elements appearing too early/late, labels missing, wrong narration-to-visual pairings.

**Pass 3:** Polish — adjust dim/glow timing, text overlay wording, easing curves.

## File inventory

After completing this process for a section, you'll have:

| File | Purpose |
|------|---------|
| `outputs/tts/mini_test/word_timestamps.json` | Whisper output: per-word timing data |
| `outputs/tts/mini_test/concat_list.txt` | ffmpeg concat manifest |
| `outputs/tts/mini_test/codecostchart_narration.wav` | Source concatenated audio |
| `remotion/public/codecostchart_narration.wav` | Audio for Remotion (copy of above) |
| `remotion/src/remotion/05a-CodeCostChartMini/constants.ts` | BEATS + composition metadata |
| `remotion/src/remotion/05a-CodeCostChartMini/CodeCostChartMini.tsx` | Animation component |
| `remotion/src/remotion/05a-CodeCostChartMini/index.ts` | Exports |
| `outputs/mini_test/codecostchart_mini.mp4` | Final rendered video |

## Applying this to other sections

To sync another composition (e.g., 06-ContextWindow):

1. Find the matching narration in `tts_script.md`
2. Identify which TTS segments cover that narration
3. Concatenate with pauses → run Whisper → get timestamps
4. Write the narration-to-animation map (Step 5)
5. Create a new composition folder (e.g., `06a-ContextWindowMini/`)
6. Build `constants.ts` with BEATS from timestamps
7. Build the component with animations keyed to those beats
8. Register in `Root.tsx`, render, review, iterate

The narration-to-animation map (Step 5) is the hard part. Everything else is mechanical.
