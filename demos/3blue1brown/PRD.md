# PRD: AI-First Video Editor

**Status:** Internal Engineering Document — derived from working prototype
**Date:** 2026-02-16
**Prototype:** `demos/3blue1brown/`

---

## 1. Product Vision & Problem Statement

### The Problem

Video production is one of the last creative workflows where iteration is punishingly slow. A director spots a timing issue at 14:32 — the fix requires a human editor to locate the source clip, adjust keyframes, re-render, re-export, and re-review. Each cycle takes minutes to hours. Most feedback dies in the gap between "I see the problem" and "I can fix it."

AI video generation (Veo, Sora, Runway) is making *creation* cheap. But the edit loop — the thing that turns a rough cut into a finished product — is still manual. This is the darning socks problem applied to video: generation costs are collapsing, but we're still patching frame by frame.

### The Vision

**Human as director, AI as editor.** The director watches the video, annotates problems (circling an area, speaking a note, typing a description), and the system:

1. Analyzes the annotation against the source spec and code
2. Proposes a fix with confidence rating
3. Applies the fix to source files
4. Re-renders the affected section
5. Stitches the result back into the full video

The director never touches a timeline, keyframe, or code editor. They just say what's wrong, and the system fixes it.

### Why This Matters

This is the same paradigm shift described in the video itself: moving from *crafting* (manually editing each frame) to *molding* (specifying intent, letting the machine produce). The review-app prototype proves this loop works end-to-end. The question is whether it can be productized.

---

## 2. Demo / Proof of Concept

### What Was Built

A complete 20-minute educational video ("Why You're Still Darning Socks") about Prompt-Driven Development, produced almost entirely through AI tooling:

| Component | Tool | Output |
|-----------|------|--------|
| Script & narrative | Human-written | `narrative/main_script.md` (39KB) |
| Voice narration | Qwen3-TTS (1.7B) | 100+ WAV segments at 24kHz mono |
| Word-level timestamps | faster-whisper | `word_timestamps.json` per section |
| Live-action footage | Google Veo 3.1 | 50+ MP4 clips (8s each, 9:16 & 16:9) |
| Animated visualizations | Remotion 4.0 + React 19 | 60 compositions, 73 named components |
| Section rendering | Remotion CLI + AWS Lambda | 7 section videos + 1 full 232MB video |
| Review & auto-fix | Express.js + Claude Opus 4.6 | `review-app/` — the key innovation |

### What It Demonstrates

1. **Spec-driven video production works.** Every shot in the video traces back to a markdown spec file. The spec is the mold; the rendered video is just plastic.
2. **AI can fix its own output.** The review-app sends Claude the spec, the Remotion source code, and a screenshot of the problem. Claude edits the source, re-renders, and the fix appears in the video.
3. **The iteration cycle is ~2 minutes.** Annotate → analyze → fix → render → stitch. Compare to traditional video editing where a comparable change takes 15-60 minutes.

---

## 3. System Architecture

### End-to-End Pipeline

```
                    PRODUCTION PIPELINE
                    ==================

  narrative/*.md ──────────────────────────────────────┐
       │                                               │
       ▼                                               ▼
  ┌──────────┐    segment_NNN.wav    ┌──────────────────────┐
  │ Qwen3-TTS │──────────────────────▶│  faster-whisper      │
  │ (render   │    24kHz mono WAV    │  word_timestamps.json │
  │  _tts.py) │                      └──────────┬───────────┘
  └──────────┘                                  │
                                                ▼
  specs/*.md ──────────────────────▶ generate_section_compositions.py
       │                                        │
       │                           ┌────────────┴────────────┐
       │                           ▼                         ▼
       │                    constants.ts              Component.tsx
       │                    (BEATS, FPS,              (visual sequence
       │                     VISUAL_SEQUENCE)          renderer)
       │                           │                         │
       ▼                           └────────────┬────────────┘
  ┌──────────┐                                  │
  │ Veo 3.1  │   MP4 clips                     ▼
  │ (generate│──────────────────▶ remotion/src/remotion/
  │ _segments│   8s, 9:16/16:9       54 composition folders
  │  .py)    │                       + 7 section wrappers
  └──────────┘                              │
                                            ▼
                               ┌─────────────────────┐
                               │  Remotion Render     │
                               │  (local CLI or       │
                               │   AWS Lambda)        │
                               └──────────┬──────────┘
                                          │
                                          ▼
                               outputs/sections/*.mp4
                                          │
                                    ffmpeg concat
                                          │
                                          ▼
                               outputs/full_video.mp4


                    REVIEW / EDIT LOOP
                    ==================

           ┌─────────────────────────────────────┐
           │         review-app (Express.js)      │
           │              port 3847               │
           └─────────────────────────────────────┘
                           │
              ┌────────────┼────────────┐
              ▼            ▼            ▼
         [Annotate]   [Analyze]    [Resolve]
              │            │            │
              │            │     ┌──────┴──────┐
              ▼            ▼     ▼      ▼      ▼
          Draw +      Claude   Fix   Render  Stitch
          Speech      reads    code  section  full
          on frame    specs    via   via      via
                      + src    CLI   Remotion ffmpeg
                      + img
```

### Data Flow: Annotation to Fixed Video

```
User presses [Space] on video
        │
        ├── Video pauses
        ├── Drawing canvas activates (1920x1080 internal)
        ├── Speech recognition starts (Web Speech API)
        │
User draws circles/arrows, speaks description
        │
User presses [Space] again
        │
        ├── Frame thumbnail captured (canvas screenshot)
        ├── Composite image created (video + drawings)
        ├── Speech text + typed text combined
        ├── Annotation saved to data/annotations.json
        │
        ▼
POST /api/annotations/:id/analyze
        │
        ├── Reads spec files from specs/{sectionDir}/
        ├── Reads Remotion source from remotion/src/remotion/{remotionDir}/
        ├── Reads relevant script section from narrative/main_script.md
        ├── Includes frame screenshot + markup composite
        │
        ▼
Claude CLI spawned:
  claude -p --model claude-opus-4-6 --output-format json
         --allowedTools Read,Glob,Write
        │
        ├── Returns JSON: severity, category, summary,
        │   technicalAssessment, suggestedFixes, relevantFiles
        │
        ▼
POST /api/annotations/:id/resolve
        │
        ├── Returns { jobId } with HTTP 202
        ├── SSE stream: GET /api/jobs/:id/stream
        │
        ▼
  ┌─── Step 1: FIX ──────────────────────────────────┐
  │ Claude CLI spawned with Edit,Write,Glob,Grep      │
  │ Scoped to: remotion/src/remotion/{remotionDir}/   │
  │ Reads: specs, source code, screenshot, analysis   │
  │ Outputs: modified .tsx files + change summary      │
  │ Returns: { filesModified, changeDescription,       │
  │            confidence: high|medium|low }           │
  └───────────────────────┬───────────────────────────┘
                          ▼
  ┌─── Step 2: RENDER ───────────────────────────────┐
  │ npx remotion render src/remotion/index.ts         │
  │   {compositionId} --output {section.mp4}          │
  │ Progress streamed via stderr parsing              │
  └───────────────────────┬───────────────────────────┘
                          ▼
  ┌─── Step 3: STITCH ──────────────────────────────┐
  │ ffmpeg -f concat -safe 0 -i concat_list.txt     │
  │   -c copy full_video.mp4                         │
  │ Reassembles all sections into final video        │
  └───────────────────────┬───────────────────────────┘
                          ▼
  Annotation marked resolved: true
  Video player reloads with updated full_video.mp4
```

---

## 4. Core Product: The AI Review/Edit Loop

This is the key innovation. Everything else (TTS, Veo, Remotion) is infrastructure. The review loop is the product.

### 4.1 Annotation Model

```
annotation = {
  id: "ann_{timestamp}_{random}",

  // What the reviewer said/drew
  text: {
    content: string,
    inputMethod: "typed" | "speech" | "mixed"
  },

  // Where in the video
  video: {
    source: "full" | "section",
    sectionId: "part1_economics" | "cold_open" | ...,
    timestamp: 5.0,                    // seconds
    timestampFormatted: "00:05.0",
    frameThumbnail: "/thumbnails/..."  // captured frame
  },

  // What they drew on the frame
  drawing: {
    canvasWidth: 1920,
    canvasHeight: 1080,
    paths: [{ tool, points, color, strokeWidth }],
    compositeImage: "/thumbnails/..."  // frame + drawings
  },

  // Claude's analysis
  analysis: {
    status: "pending" | "analyzing" | "completed",
    severity: "critical" | "high" | "medium" | "low" | "informational",
    category: "animation-timing" | "visual-design" | "readability" |
              "audio-sync" | "color-contrast" | "layout" | "typography" |
              "data-accuracy" | "transition" | "continuity" | "other",
    summary: string,
    technicalAssessment: string,
    suggestedFixes: string[],
    relevantFiles: string[],
    specReference: string
  },

  // Resolution state
  resolved: boolean,
  resolveJob: {
    jobId: string,
    status: "pending" | "running" | "done" | "error",
    step: "fixing" | "rendering" | "stitching",
    progress: 0-100,
    error: string | null
  }
}
```

### 4.2 The Spacebar Workflow

The core UX interaction, implemented in `review-app/public/app.js`:

| Press | Action |
|-------|--------|
| **Space (1st)** | Pause video, activate drawing canvas, start speech recognition |
| *User annotates* | Draw with freehand/rectangle/circle/arrow/text tools; speak or type description |
| **Space (2nd)** | Stop recording, capture frame, create composite, save annotation, resume video |

Additional keyboard shortcuts: `D` (draw mode), `M` (mic), `F/R/C/A/T` (tool select), `Ctrl+Z` (undo drawing), `Ctrl+S` (save), `K` (play/pause), arrow keys (seek).

### 4.3 Claude Integration

Two separate Claude invocations with different tool permissions:

**Analysis (read-only):**
```bash
claude -p --model claude-opus-4-6 --output-format json \
  --no-session-persistence --allowedTools Read,Glob,Write
```

Input prompt includes: spec files, main script section, Remotion source files, frame screenshot, markup composite. Output: structured severity/category/assessment JSON.

**Fix (read-write):**
```bash
claude -p --model claude-opus-4-6 --output-format json \
  --no-session-persistence --allowedTools Read,Write,Edit,Glob,Grep
```

Input prompt includes: everything from analysis + the analysis results. Claude edits Remotion source files, scoped to `remotion/src/remotion/{remotionDir}/`. Output: `{ filesModified, changeDescription, confidence }`.

### 4.4 Job Management

- **Per-section serial queue:** Only one resolve job runs per section at a time (`enqueueResolve()`)
- **SSE streaming:** Real-time progress via `GET /api/jobs/:id/stream`
- **Polling fallback:** `GET /api/jobs/:id` if EventSource fails
- **Crash recovery:** On server restart, all pending/running jobs marked as `error: "Server restarted during pipeline"`

### 4.5 Section Mapping

Seven video sections, each mapping to a spec directory, Remotion directory, and composition ID:

| Section ID | Video File | Remotion Composition | Spec Dir |
|------------|-----------|---------------------|----------|
| `cold_open` | `cold_open.mp4` | `ColdOpenSection` | `00-cold-open` |
| `part1_economics` | `part1_economics.mp4` | `Part1Economics` | `01-economics` |
| `part2_paradigm_shift` | `part2_paradigm_shift.mp4` | `Part2ParadigmShift` | `02-paradigm-shift` |
| `part3_mold` | `part3_mold.mp4` | `Part3MoldThreeParts` | `03-mold-has-three-parts` |
| `part4_precision` | `part4_precision.mp4` | `Part4PrecisionTradeoff` | `04-precision-brings-cost` |
| `part5_compound` | `part5_compound.mp4` | `Part5CompoundReturns` | `05-compound` |
| `closing` | `closing.mp4` | `ClosingSection` | `06-closing` |

---

## 5. Video Production Pipeline

### 5.1 Spec-Driven Approach

Every visual beat in the video is defined by a markdown spec file before any code is written. The `specs/` directory contains ~150+ files organized by section.

Each spec includes:
- **Tool assignment:** Remotion (animation), Veo 3.1 (live-action), or Hybrid
- **Duration and timestamp** within the video
- **Visual description** with exact animation parameters
- **Color palette** with hex codes
- **Typography** (fonts, sizes, weights)
- **Narration sync points** (which words trigger which visual events)
- **Transition** to next scene

Visual type mapping in specs:
- `veo:filename` — Veo-generated video clip
- `ComponentName` — Remotion animation component
- `title:Text` — Inline title card
- `title_over_code:Text` — Title over code backdrop
- `code_regen:label` — Code animation sequence

### 5.2 Audio Pipeline

```
narrative/tts_script.md
    │
    │  Annotations: [TONE:], [PACE:], [PAUSE:], [EMOTION:], **emphasis**
    │
    ▼
tools/tts/render_tts.py
    │
    │  Qwen3-TTS 1.7B (local model, 24kHz mono WAV)
    │  50+ tone mappings (e.g., "knowing, conspiratorial" →
    │     "as if sharing an insider insight")
    │
    ▼
segment_000.wav ... segment_NNN.wav
    │
    │  ffmpeg concat with silence gaps matching [PAUSE: Xs] annotations
    │  (silence files generated at matching 24kHz sample rate)
    │
    ▼
section_narration.wav (concatenated)
    │
    ▼
faster-whisper (base model, int8)
    │
    │  word_timestamps=True
    │
    ▼
word_timestamps.json
    │  { words: [{ word, start, end, probability }],
    │    segments: [{ start, end, text }] }
    │
    ▼
tools/generate_section_compositions.py
    │
    │  Maps Whisper segments to visual compositions
    │  Generates BEATS constants + VISUAL_SEQUENCE arrays
    │
    ▼
remotion/src/remotion/S0X-Section/constants.ts
    BEATS = {
      VISUAL_00_START: 0,    // frame numbers
      VISUAL_00_END: 148,
      VISUAL_01_START: 149,
      ...
    }
```

**Critical principle:** Audio is the source of truth, not script estimates. TTS often condenses narration, changing which visuals align with which words. Always generate audio first, then map visuals.

### 5.3 Veo Video Generation

```python
# tools/veo/generate_segments.py
operation = client.models.generate_videos(
    model="veo-3.1-generate-preview",
    prompt=enhanced_prompt,           # with character descriptions
    config=types.GenerateVideosConfig(
        aspect_ratio="9:16",          # vertical for split-screen
        number_of_videos=1
    ),
    image=reference_image             # for character consistency
)
```

- **Authentication:** Vertex AI (service account) or Gemini API key
- **Project:** `prompt-driven-development`, region `us-central1`
- **Character consistency:** Reference images are mandatory — Veo generates different-looking people every run without them
- **Split-screen:** Left/right panels generated separately in 9:16 vertical, composited via ffmpeg
- **Full-frame:** Generated directly in 16:9

### 5.4 Remotion Composition Architecture

**Scale:** 60 registered compositions in `Root.tsx`, 73 named component folders.

**Composition structure:**
```
XX-CompositionName/
├── CompositionName.tsx    # Main React component
├── constants.ts           # Props (Zod-validated), timing, colors
├── index.ts               # Exports
└── [SubComponent.tsx]     # Supporting components
```

**Key patterns:**
- All timing uses frame-based `BEATS` constants derived from Whisper timestamps
- `s2f(seconds)` helper: `Math.round(seconds * FPS)`
- Audio playback via Remotion's `<Audio>` component with `staticFile()` references
- Video clips wrapped in `<Sequence from={startFrame}>` to reset OffthreadVideo playback position
- `interpolate()` for all animation curves, with strictly increasing input ranges
- Zod schemas for type-safe composition props

**Section wrapper pattern:** Each section composition (S00-S06) contains a `VISUAL_SEQUENCE` array that switches between Veo clips and Remotion sub-compositions based on frame number, effectively creating a timeline editor in code.

### 5.5 Rendering

**Local:**
```bash
npx remotion render src/remotion/index.ts {compositionId} \
  --output ../outputs/sections/{section}.mp4 --overwrite
```

**AWS Lambda:**
- Region: `us-east-1`
- RAM: 3009 MB, Disk: 10240 MB, Timeout: 240s
- Deployed via `remotion/deploy.mjs`
- API endpoints: `src/app/api/lambda/render/route.ts`, `.../progress/route.ts`

---

## 6. Tech Stack & Dependencies

### Core

| Layer | Technology | Version | Purpose |
|-------|-----------|---------|---------|
| Animation framework | Remotion | 4.0.410 | Programmatic video composition |
| UI framework | React | 19.2.3 | Component rendering |
| Web framework | Next.js | 16.0.10 | Remotion web UI + Lambda API |
| Styling | Tailwind CSS | 4.0.3 | Component styling |
| Schema validation | Zod | 3.22.3 | Composition prop validation |
| Video generation | Google Veo 3.1 | Preview | AI-generated live-action footage |
| TTS | Qwen3-TTS | 1.7B | Narration audio generation |
| Transcription | faster-whisper | base/int8 | Word-level timestamps |
| AI editor | Claude Opus 4.6 | CLI | Analysis + code fixes |
| Video processing | ffmpeg | System | Concat, composite, frame extract |
| Cloud rendering | AWS Lambda | @remotion/lambda | Distributed rendering |
| Review server | Express.js | 4.21.0 | Annotation API + video streaming |

### Python Tools

| Package | Purpose |
|---------|---------|
| `google-genai` | Vertex AI / Veo API client |
| `faster-whisper` | Whisper transcription |
| `transformers` | Qwen3-TTS model loading |
| `soundfile` | WAV file I/O |

### Review App

| Package | Purpose |
|---------|---------|
| `express` | HTTP server |
| `jest` + `supertest` | Testing |
| Web Speech API | Browser-native speech recognition |

---

## 7. Current State Assessment

### What Works

| Capability | Status | Notes |
|------------|--------|-------|
| Spec → TTS → Whisper → BEATS constants | **Solid** | Reliable pipeline, well-documented |
| Veo clip generation with references | **Works** | Character consistency requires reference images every time |
| Remotion composition rendering | **Solid** | 60 compositions render successfully |
| Full video assembly (7 sections) | **Works** | ffmpeg concat with codec copy |
| Spacebar annotation workflow | **Works** | Drawing + speech + frame capture |
| Claude analysis of annotations | **Works** | Structured severity/category output |
| Claude auto-fix of Remotion source | **Works** | Scoped to section directory |
| Section re-render after fix | **Works** | Remotion CLI with progress monitoring |
| Full video re-stitch | **Works** | Fast — codec copy, no re-encoding |
| SSE job streaming | **Works** | With polling fallback |

### What's Prototype-Quality (Duct Tape)

| Area | Issue | Impact |
|------|-------|--------|
| **Persistence** | Annotations stored in a flat JSON file (`data/annotations.json`) | No concurrent access, no backup, no history |
| **Auth** | None | Single-user only |
| **Claude spawning** | New CLI process per analysis/fix — cold start every time | ~10s overhead per invocation |
| **JSON extraction** | Three fallback strategies for parsing Claude's output (direct parse, code fence, brace matching) | Fragile; depends on Claude's output format |
| **Section mapping** | Hardcoded array of 7 sections with manual spec/remotion/composition mapping | Adding sections requires server code change |
| **Video streaming** | Range request support but no caching, CDN, or adaptive bitrate | Fine for local, won't scale |
| **Drawing state** | Canvas paths serialized as JSON arrays | No undo history, no layer management |
| **Error recovery** | Jobs marked as error on server restart, no retry | Manual re-run required |
| **Thumbnail storage** | Local filesystem `data/thumbnails/` | Not backed up, grows unbounded |
| **Rendering** | Full Remotion render for any change, even single-frame fixes | Rendering a 2-minute section takes ~60s for a 1-line color change |

### What's Missing

| Feature | Why It Matters |
|---------|---------------|
| **Version control for fixes** | No way to revert a bad Claude fix. Once it edits the .tsx file, the old version is gone (unless git tracked). |
| **Multi-annotation batching** | Each annotation triggers a separate fix → render → stitch cycle. Five annotations on the same section = five full renders. |
| **Diff preview** | No way to see what Claude will change before it changes it. The fix is applied blindly. |
| **Selective re-render** | Rendering is per-section. Can't re-render just the 3 seconds around the fix. |
| **Asset management** | Veo clips, TTS segments, and reference images are scattered across `outputs/`, `remotion/public/`, and `references/`. No manifest or DAM. |
| **Collaboration** | Single-user, single-machine. No shared annotation state. |
| **Cost tracking** | No visibility into Claude API costs, Veo generation costs, or Lambda rendering costs per fix. |

---

## 8. Key Technical Learnings

These are hard-won lessons from production, documented in `docs/RENDERING_METHODOLOGY.md` and `docs/audio-synced-animation-process.md`.

### 8.1 OffthreadVideo Timing Bug

Remotion's `<OffthreadVideo>` seeks to the composition's absolute frame time, not relative to when the clip appears. If a clip is 8 seconds long and the segment starts at 10 seconds, OffthreadVideo tries to seek to 10s in an 8s clip, showing a frozen last frame.

**Fix:** Always wrap video clips in a `<Sequence>`:
```tsx
<Sequence from={BEATS.VISUAL_03_START}>
  <OffthreadVideo src={staticFile("clip.mp4")} />
</Sequence>
```

### 8.2 interpolate() Requires Strictly Increasing Input

```tsx
// WRONG — duplicate 10 causes runtime error
interpolate(frame, [0, 10, 10, 25], [1, 1, 1, 0])

// CORRECT — use 11 instead of second 10
interpolate(frame, [0, 10, 11, 25], [1, 1, 1, 0])
```

### 8.3 Character Consistency in Veo

Veo generates different-looking people every run. Without reference images, the "developer" character looks different in every clip. Reference images must match the scene type — close-ups work better than wide shots as references.

### 8.4 Audio Is Source of Truth

TTS narration is often condensed from the full script and reshuffles which visuals belong to which audio segments. Never estimate timing from the script — always generate audio first, run Whisper, then map visuals to actual word timestamps.

### 8.5 Visual Type Must Match Segment Duration

A 10-second Remotion animation crammed into a 1-2 second window shows only its first frames. Match the visual type to the available duration. Short segments need simple visuals; complex animations need long segments.

### 8.6 Frame Math for Short Segments

When a segment is only 1-2 seconds (30-60 frames at 30fps), animations must be compressed to complete within 80% of available frames. Leave 20% headroom for easing.

### 8.7 File Size as Smoke Test

For a 19-second rendered video:
- <5 MB = Multiple frozen/black segments (broken)
- 5-10 MB = Some segments are still frames (partially broken)
- 10-20 MB = Normal range (healthy)
- \>25 MB = Unusual; check for duplicated clips

### 8.8 Narration-Synced Animation Principles

1. Visual elements appear when the narrator mentions them, not before
2. Labels appear immediately when their line starts drawing, not after
3. Animation mirrors the script's rhetorical structure
4. Every narration phrase should have a visual response
5. No orphaned visuals — nothing appears that the narrator hasn't explained

---

## 9. Product Requirements for V1

### 9.1 Core Loop (Must Have)

**P0 — The review/fix/render cycle, productized:**

- [ ] **Project import:** Load a Remotion project with specs, define sections and composition mappings via config file (not hardcoded)
- [ ] **Video player with annotation:** Spacebar workflow (pause → draw → speak → save → resume), drawing tools (freehand, rectangle, circle, arrow, text), speech-to-text input
- [ ] **AI analysis:** Send annotation context (frame, drawing, text, spec, source code) to Claude; return structured assessment with severity/category/fixes
- [ ] **Diff preview:** Show proposed code changes before applying. User can accept, reject, or edit.
- [ ] **AI fix:** Apply accepted changes to source files with git commit per fix (automatic rollback support)
- [ ] **Section render:** Re-render only the affected section
- [ ] **Full stitch:** Reassemble full video from sections
- [ ] **Progress streaming:** Real-time SSE updates through the fix → render → stitch pipeline

### 9.2 Reliability (Must Have)

**P0 — Things that are currently broken or fragile:**

- [ ] **Database-backed persistence:** Replace `annotations.json` with SQLite or Postgres. Support concurrent access, annotation history, and backup.
- [ ] **Structured Claude output:** Use Claude's tool_use mode or structured output instead of free-form JSON parsing with three fallback strategies
- [ ] **Git integration:** Auto-commit before and after every Claude fix. Enable `git diff` preview and `git revert` for bad fixes.
- [ ] **Job retry:** Allow retrying failed resolve jobs without re-analyzing
- [ ] **Batch fixes:** Queue multiple annotations on the same section, apply all fixes, render once

### 9.3 Efficiency (Should Have)

**P1 — Performance and cost improvements:**

- [ ] **Incremental rendering:** Render only the frames around the fix (Remotion supports `--frames` flag), composite into existing section video
- [ ] **Claude session reuse:** Keep a warm Claude session per section instead of cold-starting the CLI for every analysis/fix
- [ ] **Parallel section renders:** If fixes touch different sections, render them concurrently
- [ ] **Cost dashboard:** Track and display Claude API, Veo, and Lambda costs per annotation and per session

### 9.4 Collaboration (Should Have)

**P1 — Multi-user support:**

- [ ] **User accounts:** Basic auth with roles (director, editor, viewer)
- [ ] **Shared annotation state:** WebSocket-based real-time sync of annotations across clients
- [ ] **Comment threads:** Discussion on annotations before resolving
- [ ] **Assignment:** Assign annotations to team members or to AI

### 9.5 Production Pipeline Integration (Nice to Have)

**P2 — The full spec-driven pipeline as a managed workflow:**

- [ ] **Spec editor:** Edit markdown specs in-app with live preview
- [ ] **TTS generation:** Trigger Qwen3-TTS rendering from the UI
- [ ] **Veo generation:** Generate and manage video clips with reference image tracking
- [ ] **Asset manager:** Central registry of all clips, audio segments, reference images, and generated compositions
- [ ] **Timeline view:** Visual representation of section composition with drag-to-reorder

---

## 10. Open Questions & Risks

### Technical Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| **Veo API stability** | High | Preview API; could change or be rate-limited. No SLA. Need fallback video generation (Runway, Sora, local models). |
| **Claude fix quality** | High | No guarantee fixes are correct. Diff preview is essential. Need rollback. Consider confidence threshold below which human review is required. |
| **Rendering cost at scale** | Medium | AWS Lambda rendering at $0.01-0.05/section-render. A 50-annotation review session = $0.50-2.50 in rendering alone, plus Claude API costs. |
| **Remotion lock-in** | Medium | Entire pipeline assumes Remotion as the rendering engine. Switching to After Effects, DaVinci, or a different framework would require rewriting the fix pipeline. |
| **Qwen3-TTS quality** | Low | Local model, good enough for prototyping. Production may need ElevenLabs or similar for more natural speech. |
| **ffmpeg concat limitations** | Low | Codec copy works only when all sections have identical encoding params. Re-encoding on stitch would add minutes. |

### Product Questions

| Question | Options | Notes |
|----------|---------|-------|
| **Who is the user?** | (a) Internal teams making AI-generated video, (b) External creators using Remotion, (c) Any video creator | Determines scope of "source code" — Remotion .tsx vs. After Effects project vs. general video |
| **Real-time or batch?** | (a) Fix immediately after annotation, (b) Batch all annotations then fix all at once | Batch is more efficient (one render per section), real-time feels more magical |
| **Claude vs. general LLM?** | (a) Claude-only (current), (b) Pluggable LLM backend | Claude's Edit tool and code understanding are key advantages; unclear if alternatives can match |
| **Self-hosted or cloud?** | (a) Local Express server (current), (b) Cloud-hosted SaaS | Local avoids video upload latency; cloud enables collaboration |
| **Scope of "fix"** | (a) Remotion source code only (current), (b) Also regenerate Veo clips, (c) Also re-record TTS | Each expansion multiplies complexity and cost |

### Known Limitations

1. **No audio fixes.** The prototype can only fix visual/animation issues. If the narration timing is wrong, the TTS must be manually regenerated.
2. **Section granularity.** Fixes trigger a full section re-render (30s-4min of video) even for a 1-frame change. Remotion's `--frames` flag could narrow this, but stitching partial renders into an existing section requires additional ffmpeg work.
3. **Single video format.** The pipeline assumes one output resolution (1920x1080) and one codec. No adaptive bitrate, no mobile-optimized renders.
4. **No undo beyond git.** The prototype has no in-app undo for applied fixes. Git is the only safety net, and it's not integrated into the UI.

---

## Appendix A: API Surface (review-app/server.js)

### Video

| Method | Path | Description |
|--------|------|-------------|
| GET | `/video/full` | Stream full video with range requests |
| GET | `/video/sections/:file` | Stream section video with range requests |

### Annotations

| Method | Path | Description |
|--------|------|-------------|
| GET | `/api/annotations` | List all annotations |
| POST | `/api/annotations` | Create annotation (auto-ID) |
| PUT | `/api/annotations/:id` | Update annotation |
| DELETE | `/api/annotations/:id` | Delete annotation |
| POST | `/api/annotations/:id/analyze` | Trigger Claude analysis |
| POST | `/api/annotations/:id/resolve` | Start fix → render → stitch pipeline (returns `{ jobId }`) |

### Analysis

| Method | Path | Description |
|--------|------|-------------|
| POST | `/api/analyze` | One-off analysis (no annotation created) |

### Jobs

| Method | Path | Description |
|--------|------|-------------|
| GET | `/api/jobs/:id` | Poll job status |
| GET | `/api/jobs/:id/stream` | SSE stream of job progress |

### Metadata

| Method | Path | Description |
|--------|------|-------------|
| GET | `/api/sections` | List section metadata |
| POST | `/api/thumbnails` | Upload base64 frame capture |
| GET | `/api/export` | Download annotations.json |

---

## Appendix B: File Map

```
demos/3blue1brown/
├── narrative/
│   ├── main_script.md            # Full script with visual descriptions (39KB)
│   ├── tts_script.md             # TTS-optimized script with annotations (20KB)
│   └── tts_cold_open.md          # Cold open excerpt
│
├── specs/
│   ├── 00-cold-open/             # 8 specs + prompts/
│   ├── 01-economics/             # 13 specs + README + prompts/
│   ├── 02-paradigm-shift/        # 11 specs + README + prompts/
│   ├── 03-mold-has-three-parts/  # Mold mechanics specs
│   ├── 04-precision-brings-cost/ # Precision requirement specs
│   └── 05-compound/              # Compound cost specs
│
├── remotion/
│   ├── src/remotion/
│   │   ├── Root.tsx              # 60 composition registrations
│   │   ├── 01-ColdOpen/         # through 51-SockMetaphorFinal/
│   │   ├── S00-ColdOpen/        # Section wrappers (S00-S06)
│   │   └── examples/
│   ├── deploy.mjs                # AWS Lambda deployment
│   ├── config.mjs                # Lambda config (region, RAM, timeout)
│   └── package.json              # Remotion 4.0.410, React 19, Next.js 16
│
├── tools/
│   ├── tts/
│   │   ├── render_tts.py         # Qwen3-TTS rendering
│   │   ├── sync_audio_pipeline.py # Concat + Whisper
│   │   └── render_full.py        # Full pipeline
│   ├── veo/
│   │   ├── generate_segments.py  # Veo 3.1 video generation
│   │   ├── generate_references.py # Reference image creation
│   │   └── composite_segments.py # Split-screen compositing
│   └── generate_section_compositions.py  # Whisper → BEATS → Remotion
│
├── review-app/
│   ├── server.js                 # Express API (862 lines)
│   ├── server.test.js            # Jest test suite
│   ├── package.json              # express, jest, supertest
│   ├── public/
│   │   ├── index.html            # Editor UI
│   │   ├── app.js                # Keyboard shortcuts, spacebar workflow
│   │   ├── video-player.js       # Video playback + frame capture
│   │   ├── canvas-overlay.js     # Drawing tools (5 tools, 314 lines)
│   │   ├── annotation-panel.js   # CRUD + resolve pipeline UI (589 lines)
│   │   ├── speech-input.js       # Web Speech API wrapper
│   │   ├── api-client.js         # Fetch wrapper + SSE
│   │   └── styles.css            # Dark theme, severity badges
│   └── data/
│       ├── annotations.json      # Flat file persistence
│       └── thumbnails/           # Frame captures
│
├── docs/
│   ├── RENDERING_METHODOLOGY.md  # Production lessons (354 lines)
│   └── audio-synced-animation-process.md  # Audio sync methodology
│
├── outputs/
│   ├── full_video.mp4            # Final video (232MB)
│   ├── sections/                 # 7 section videos + concat_list.txt
│   ├── tts/                      # Audio segments + timestamps
│   └── veo/                      # Generated video clips
│
├── references/                   # Character reference images for Veo
├── audits/                       # Frame-by-frame QA reports
├── models/                       # Local Qwen3-TTS weights
└── archive/                      # Historical assets
```
