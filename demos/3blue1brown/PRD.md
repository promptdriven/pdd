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

**Human as director, AI as entire crew.** A single webapp is the control plane for the full video production pipeline — from source script to finished video. The director:

1. **Writes or imports** a source script
2. **Triggers generation** of TTS audio, visual specs, Veo clips, and Remotion compositions — each step orchestrated by the webapp calling Claude Code
3. **Reviews** the rendered video, annotating problems (circling an area, speaking a note, typing a description)
4. **Approves fixes** proposed by Claude, which are applied, re-rendered, and stitched back automatically

The director never touches a timeline, keyframe, terminal, or code editor. The webapp calls Claude Code to handle every step that was previously manual — generating TTS scripts, writing specs, authoring Remotion components, staging assets between pipeline stages, and fixing issues found during review.

### Why This Matters

This is the same paradigm shift described in the video itself: moving from *crafting* (manually editing each frame) to *molding* (specifying intent, letting the machine produce). The prototype proves two things: (1) the review/fix loop works end-to-end, and (2) Claude Code can execute every "glue" step in the production pipeline. The product unifies both into a single webapp where the human directs and the AI produces.

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

### General Pipeline

Any video produced by this system follows the same fork-and-converge pattern. A single source script splits into parallel tracks — audio, animation specs, and video clips — then all tracks merge at render time.

```
                            ┌──────────────────────┐
                            │  Source Script        │
                            │  (human-written)      │
                            │                       │
                            │  Narration text +     │
                            │  visual descriptions  │
                            └──────────┬────────────┘
                                       │
              ┌────────────────────────┼─────────────────────────┐
              │ Claude Code            │ Claude Code              │ Claude Code
              │ extracts narration,    │ expands visual           │ generates video
              │ adds TTS annotations   │ descriptions into        │ generation prompts
              │                        │ detailed specs           │
              ▼                        ▼                          ▼
    ┌──────────────────┐    ┌──────────────────────┐    ┌──────────────────┐
    │ TTS Script        │    │ Visual Specs          │    │ Video Prompts     │
    │                   │    │ (per-shot markdown)   │    │ (per-clip)        │
    │ [TONE:] [PACE:]   │    │ Animation params,     │    │ Character desc,   │
    │ [PAUSE:] emphasis │    │ color palettes,        │    │ scene, camera,    │
    │                   │    │ timing, code scaffold │    │ lighting          │
    └────────┬─────────┘    └──────────┬────────────┘    └────────┬─────────┘
             │                         │                          │
    ═══ AUDIO TRACK ═══      ═══ ANIMATION TRACK ═══    ═══ VIDEO TRACK ═══
             │                         │                          │
             ▼                         ▼                          ▼
    TTS engine                Claude Code writes         Imagen: reference
    (segment WAVs)             Remotion compositions     portraits for
             │                 from specs                character consistency
             ▼                         │                          │
    Concat with pauses                 │                          ▼
    (per section)                      │                 Veo: clip generation
             │                         │                 with frame chaining
             ▼                         │                 (last frame of clip N
    Whisper transcription              │                  → reference for N+1)
    (word-level timestamps)            │                          │
             │                         │                          ▼
             ▼                         │                 Compositing (ffmpeg)
    Section composition                │                 + asset staging
    generator (BEATS +                 │                          │
    VISUAL_SEQUENCE from               │                          ▼
    timestamps)                        │                 remotion/public/*.mp4
             │                         │                 remotion/public/*.wav
             ▼                         │
    Section wrappers ──────────────────┘
    (initially generated,
     then refined by
     Claude Code)
                           │
              ═══ CONVERGENCE ═══
                           │
                           ▼
              ┌─────────────────────────┐
              │  Remotion Render         │
              │  (local CLI or Lambda)   │
              │                          │
              │  All tracks merge:       │
              │  - <Audio> from WAVs     │
              │  - <OffthreadVideo>      │
              │    from video clips      │
              │  - Animated components   │
              │  - BEATS timing from     │
              │    Whisper timestamps    │
              └────────────┬────────────┘
                           │
                           ▼
              Section MP4s → ffmpeg concat → Full Video
                           │
              ═══ REVIEW LOOP ═══
                           │
                           ▼
              ┌─────────────────────────┐
              │  Webapp (review-app)    │
              │  Annotate → Analyze →   │
              │  Fix → Render → Stitch  │
              └─────────────────────────┘
```

**In the product, the webapp controls the entire pipeline above** — not just the review loop at the bottom. Each "Claude Code" step in the diagram becomes a server-initiated Claude Code invocation triggered by the UI. Each "Fully automated" step (TTS, Whisper, Veo, Remotion render) becomes a job the server spawns and streams progress for. The user drives every stage from the same interface.

### Automation Model

Every step in the pipeline is one of three types. This pattern held across the demo and would hold for any video:

| Step | Method | Automation |
|------|--------|------------|
| Write source script | Human | Manual |
| Generate TTS script | Claude Code | LLM-directed |
| Generate visual specs | Claude Code | LLM-directed (iterative) |
| Generate video prompts | Claude Code | LLM-directed |
| Render TTS audio | TTS engine | Fully automated |
| Concatenate sections with pauses | Concat pipeline | Fully automated |
| Transcribe with word timestamps | Whisper | Fully automated |
| Generate character reference images | Imagen | Fully automated |
| Generate video clips (with frame chaining) | Veo | Fully automated |
| Stage video clips to Remotion | Claude Code | LLM-directed |
| Write Remotion compositions | Claude Code (from specs) | LLM-directed |
| Generate section wrapper scaffolding | Composition generator | Fully automated |
| Refine section wrappers | Claude Code | LLM-directed |
| Render sections | Remotion CLI / Lambda | Fully automated |
| Stitch full video | ffmpeg concat | Fully automated |
| Audit renders against specs | Parallel Claude Code agents | LLM-directed |
| Review and auto-fix | review-app + Claude | Automated loop |

The key insight: **Claude Code is the orchestrator.** The automated scripts handle individual pipeline stages, but Claude Code acts as the glue — generating intermediate artifacts, staging files between pipelines, and refining scaffolded output. In the prototype, a human drove Claude Code from the terminal. In the product, **the webapp drives Claude Code programmatically** — every "LLM-directed" step becomes a server-side Claude Code invocation triggered by a button in the UI.

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

## 4. Core Product: The Webapp

The webapp is the single control plane for the entire pipeline. In the prototype, the review/fix loop is the most polished piece — but the product extends that same pattern (user triggers action → server calls Claude Code / spawns job → streams progress → returns result) to every pipeline stage.

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

The server maintains a section registry that maps each video section to its spec directory, Remotion directory, and composition ID. This registry drives the entire review loop — analysis scopes Claude to the correct spec/source files, and rendering targets the correct composition.

```
section = {
  id: string,              // e.g. "intro"
  label: string,           // Display name
  videoFile: string,       // e.g. "intro.mp4"
  specDir: string,         // e.g. "00-intro"
  remotionDir: string,     // e.g. "S00-Intro"
  compositionId: string    // e.g. "IntroSection"
}
```

In the prototype, this is a hardcoded array in `server.js`. In V1, this should be a config file (`sections.json` or similar) loaded at startup, so new videos don't require code changes.

> **In the demo (7 sections):**
>
> | Section ID | Video File | Remotion Composition | Spec Dir |
> |------------|-----------|---------------------|----------|
> | `cold_open` | `cold_open.mp4` | `ColdOpenSection` | `00-cold-open` |
> | `part1_economics` | `part1_economics.mp4` | `Part1Economics` | `01-economics` |
> | `part2_paradigm_shift` | `part2_paradigm_shift.mp4` | `Part2ParadigmShift` | `02-paradigm-shift` |
> | `part3_mold` | `part3_mold.mp4` | `Part3MoldThreeParts` | `03-mold-has-three-parts` |
> | `part4_precision` | `part4_precision.mp4` | `Part4PrecisionTradeoff` | `04-precision-brings-cost` |
> | `part5_compound` | `part5_compound.mp4` | `Part5CompoundReturns` | `05-compound` |
> | `closing` | `closing.mp4` | `ClosingSection` | `06-closing` |

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

The audio pipeline follows a fixed five-stage pattern for any video: script extraction → TTS rendering → section grouping → transcription → timing constant generation.

```
Source Script
    │
    │  Full script with narration text + visual description blocks
    │
    ▼
Claude Code (one-time generation)
    │
    │  Extracts narration text (strips visual descriptions)
    │  Adds TTS annotations: [TONE:], [PACE:], [PAUSE:], [EMOTION:]
    │  Adds emphasis markers for delivery
    │  Condenses phrasing for natural speech
    │
    ▼
TTS Script
    │
    │  Pure narration with voice direction annotations
    │  Sections separated by --- dividers
    │
    ▼
TTS Renderer (render_tts.py) — parse + generate
    │
    │  1. Parse: extract segments with tone/pace/emotion metadata
    │  2. Generate: TTS engine produces individual WAV segments
    │  3. Output: per-segment WAVs + full concatenated audio
    │
    ▼
Per-segment WAV files
    │
    ▼
Sync Pipeline (sync_audio_pipeline.py) — group + concatenate + transcribe
    │
    │  1. Groups segments by section (segment-to-section mapping)
    │  2. Concatenates with silence gaps matching [PAUSE: Xs] durations
    │     (np.zeros at sample rate — not ffmpeg)
    │  3. Copies section WAVs to remotion/public/ for <Audio> playback
    │
    ▼
Per-section narration WAVs
    │
    │  Whisper transcription (word_timestamps=True)
    │
    ▼
Per-section word_timestamps.json
    │  { words: [{ word, start, end, probability }],
    │    segments: [{ start, end, text }] }
    │
    ▼
Section Composition Generator (generate_section_compositions.py)
    │
    │  Maps Whisper segments to visual compositions
    │  Generates BEATS constants + VISUAL_SEQUENCE arrays
    │
    ▼
remotion/src/remotion/{SectionDir}/constants.ts
    BEATS = {
      VISUAL_00_START: 0,    // frame numbers
      VISUAL_00_END: 148,
      VISUAL_01_START: 149,
      ...
    }
```

**Critical principle:** Audio is the source of truth, not script estimates. TTS condenses narration and reshuffles which visuals align with which words. Always generate audio first, run Whisper, then map visuals to actual word timestamps.

> **In the demo:**
> - Source script: `narrative/main_script.md` (39KB) with `NARRATOR:` text + `[VISUAL:]` blocks
> - TTS script: `narrative/tts_script.md` (20KB), ~103 segments
> - TTS engine: Qwen3-TTS 1.7B (local, 24kHz mono, speaker "Aiden"), 50+ tone mappings
> - Segment output: `outputs/tts/segment_000.wav` through `segment_111.wav` (112 files)
> - Section grouping (hardcoded ranges in `sync_audio_pipeline.py`): cold_open: 105-110, part1: 0-29, part2: 31-45, part3: 47-71, part4: 73-80, part5: 82-90, closing: 92-100
> - Section WAVs: `outputs/tts/{section}/{section}_narration.wav` (7 files)
> - Timestamps: `outputs/tts/{section}/word_timestamps.json` (7 files, faster-whisper base/int8)

### 5.3 Video Generation (Imagen + Veo)

Video generation follows a three-phase pattern: reference image creation, clip generation with frame chaining, and asset staging to the Remotion project.

#### Phase 1: Reference Images (Imagen)

Before generating video clips, create character reference portraits using an image generation model. These seed Veo with consistent character appearances.

```python
# tools/veo/generate_references.py
result = client.models.generate_images(
    model="imagen-3.0-generate-002",
    prompt=character_prompt,
    config=types.GenerateImagesConfig(
        number_of_images=1,
        person_generation="allow_adult"
    )
)
```

Reference images are stored in `references/{section}/` and include detailed character descriptions (age, clothing, accessories) in the prompt. Close-up portraits work better as reference images than wide shots.

#### Phase 2: Clip Generation with Frame Chaining

Each clip is generated from a prompt (extracted from the spec's `## Veo Prompt` block) plus a reference image. The reference can be either an Imagen portrait or the last frame of the previous clip.

```python
# tools/veo/generate_segments.py
operation = client.models.generate_videos(
    model="veo-3.1-generate-preview",
    prompt=enhanced_prompt,
    config=types.GenerateVideosConfig(
        aspect_ratio="9:16",          # vertical for split-screen, or 16:9 for full-frame
        number_of_videos=1
    ),
    image=reference_image             # Imagen portrait OR last frame of previous clip
)
```

**Frame chaining** is the key mechanism for character consistency across clips. Rather than using the same static reference for every clip, each script extracts the last frame of clip N and feeds it as the reference for clip N+1:

```
Imagen portrait → Veo clip A → extract last frame → Veo clip B →
  extract last frame → Veo clip C → ...
```

This chaining can also work **across sections**, creating visual continuity across the full video. Frame extraction uses ffprobe + ffmpeg:

```bash
ffprobe -v error -show_entries format=duration -of csv=p=0 clip.mp4
ffmpeg -ss {duration - 0.1} -i clip.mp4 -vframes 1 -q:v 2 last_frame.png
```

Common clip patterns:
- **Split-screen:** Left/right panels generated separately in 9:16 vertical, composited via ffmpeg into 16:9
- **Full-frame:** Generated directly in 16:9
- **Parallel generation:** `ThreadPoolExecutor` for generating independent clips concurrently
- **Post-processing:** Color grading (sepia, vignette) via ffmpeg `colorchannelmixer`

#### Phase 3: Asset Staging

Veo scripts write to `outputs/veo/{section}/{raw,composited,frames}/`. A separate step stages clips to `remotion/public/` where Remotion's `staticFile()` can find them. In the prototype, this was performed by Claude Code executing `cp` commands — not by any script.

The destination filenames must match the `staticFile()` references in the composition code. The `generate_section_compositions.py` script defines expected names via `veo:` prefixed entries in its visual sequence data (e.g., `"veo:intro_clip_01"`), which translates to `staticFile("intro_clip_01.mp4")`. Claude Code closed the loop by copying files to match these references.

In V1, asset staging should be automated — either by having Veo scripts write directly to `remotion/public/` with standardized names, or by maintaining a manifest that maps output paths to `staticFile()` references.

> **In the demo:**
>
> *Reference images:*
> - `references/cold-open/developer_reference.png` — 32-year-old male, dark navy hoodie, black-framed glasses
> - `references/cold-open/grandmother_reference.png` — 75-year-old woman, cream cardigan, wire-rimmed spectacles
> - `references/part-1/` — alternate reference set for economics section
>
> *Frame chaining across sections:* Cold open segment 01e's last frames (`01e_left_last.png`, `01e_right_last.png`) reused as references for economics segment 07. Segments 07→08→09 form their own dependency chain.
>
> *Generation scripts (9 total):*
>
> | Script | Section | Notable Features |
> |--------|---------|-----------------|
> | `generate_segments.py` | 00-cold-open | Main script; `--use-references`, `--separate-sides`, `--sequential` flags |
> | `generate_references.py` | — | Imagen 3.0 portrait generation (not Veo) |
> | `composite_segments.py` | 00-cold-open | ffmpeg split-screen compositing (left 9:16 + right 9:16 → 16:9) |
> | `generate_paradigm_shift.py` | 02-paradigm-shift | Generates segments 01, 02, 04, 05, 07 from section specs |
> | `generate_section_04.py` | 04-precision | Parallel generation via `ThreadPoolExecutor(max_workers=4)` |
> | `generate_segment_07.py` | 01-economics | Cross-section reference reuse; sepia color grading |
> | `generate_segment_08.py` | 01-economics | Chained from segment 07's last frame |
> | `generate_segment_09.py` | 01-economics | Chained from segment 08's last frame |
> | `generate_segment_2_01.py` | 02-paradigm-shift | Standalone factory floor shot |
>
> *Asset staging examples:*
>
> | Source (`outputs/veo/`) | Destination (`remotion/public/`) |
> |---|---|
> | `00-cold-open/composited/01a_establish_split_screen.mp4` | `cold_open_01a_establish.mp4` |
> | `02-paradigm-shift/raw/04_defect_discovered.mp4` | `veo_defect_discovered.mp4` |
> | `04-precision-tradeoff/composited/01_split_3d_vs_mold.mp4` | `split_3d_vs_mold.mp4` |

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

### 5.6 Multi-Agent Audit Pipeline

After rendering, parallel Claude Code agents audit every visual segment against its spec. Each agent:

1. Renders a still frame at the segment midpoint using `npx remotion still`
2. Compares the frame against the spec's visual description, color palette, animation state, and narration sync point
3. Writes an `AUDIT_*.md` file with pass/fail verdict and technical notes

Agents run in parallel (one per section). Each agent receives a batch of specs to audit and works independently. Results are aggregated into section-level and master sweep reports.

**Output structure:**
- `audits/AUDIT_SWEEP_{date}.md` — master sweep report with pass/fail counts
- `audits/AUDIT_BRIEFS.md` — pre-prepared audit briefs with batch breakdowns
- `audits/AUDIT_{section}.md` — section-level summaries
- `specs/{section}/AUDIT_*.md` — spec-level audit files with frame-by-frame analysis
- `specs/{section}/AUDIT_SUMMARY.md` — per-section rollup

Audit files include version iterations (e.g., `AUDIT_S01_V0.md` through `AUDIT_S01_V23.md`) when issues are found and re-audited after fixes.

> **In the demo:** 7 agents audited 82 scenes across 7 sections, producing 136 audit files. Master sweep report: 81 PASS, 1 NEEDS_FIX.

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
| Reference images | Google Imagen 3.0 | `imagen-3.0-generate-002` | Character portrait generation for Veo consistency |
| Video generation | Google Veo 3.1 | Preview | AI-generated live-action footage |
| TTS | Qwen3-TTS | 1.7B (local, ~4.5GB) | Narration audio generation |
| Transcription | faster-whisper | base/int8 | Word-level timestamps |
| AI editor | Claude Opus 4.6 | CLI | Analysis + code fixes |
| Video processing | ffmpeg | System | Concat, composite, frame extract |
| Cloud rendering | AWS Lambda | @remotion/lambda | Distributed rendering |
| Review server | Express.js | 4.21.0 | Annotation API + video streaming |

### Python Tools

| Package | Purpose |
|---------|---------|
| `google-genai` | Vertex AI / Veo + Imagen API client |
| `faster-whisper` | Whisper transcription |
| `qwen_tts` | Qwen3-TTS model loading and inference |
| `transformers` | HuggingFace model infrastructure |
| `soundfile` | WAV file I/O |

### Model Setup

Qwen3-TTS runs locally and requires downloading ~4.5GB of model weights:

```
models/
├── Qwen3-TTS-12Hz-1.7B-CustomVoice/   # 3.8GB (model.safetensors + config)
└── Qwen3-TTS-Tokenizer-12Hz/          # 682MB (speech tokenizer)
```

`render_tts.py` loads from the local `models/` directory. `render_full.py` loads from HuggingFace Hub (cached). There is no setup script — models were downloaded manually via HuggingFace Hub. The `qwen_tts` Python package is required but not listed in any requirements file within the demo directory.

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

Veo generates different-looking people every run. The solution is two-layered:

1. **Imagen-generated reference portraits** seed each section with a consistent character appearance
2. **Frame chaining** propagates consistency across clips — the last frame of clip N becomes the reference for clip N+1, creating a visual chain that drifts less than using a static portrait for every clip

Close-up portraits work better as reference images than wide shots. Cross-section chaining (cold open frames reused in economics) maintains continuity across the full video.

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

### 9.1 Production Pipeline (Must Have)

**P0 — The webapp controls the full pipeline, not just the review loop:**

- [ ] **Project setup:** Create a new video project from a source script. Define sections, configure TTS voice/model, set output resolution.
- [ ] **Script → TTS script generation:** Trigger Claude Code to extract narration and add TTS annotations. Review/edit the generated TTS script in-app.
- [ ] **TTS rendering:** Trigger TTS generation from the UI. Preview audio per-segment. Re-generate individual segments.
- [ ] **Audio sync pipeline:** Trigger section grouping, silence insertion, Whisper transcription. Display word-level timestamps.
- [ ] **Spec generation:** Trigger Claude Code to generate visual specs from the source script. Edit specs in-app with live preview.
- [ ] **Veo generation:** Trigger reference image creation (Imagen) and clip generation (Veo) from the UI. Manage frame chaining dependencies. Preview clips inline.
- [ ] **Composition generation:** Trigger Claude Code to write Remotion compositions from specs. Trigger section wrapper scaffolding. Preview individual compositions.
- [ ] **Asset staging:** Automated staging of Veo clips and TTS audio to `remotion/public/` with manifest tracking (replacing the manual Claude Code `cp` pattern).
- [ ] **Section render + stitch:** Render sections (local CLI or Lambda), assemble full video.
- [ ] **Progress streaming:** Real-time SSE/WebSocket updates for every pipeline stage — not just the fix loop.

### 9.2 Review/Fix Loop (Must Have)

**P0 — The review/fix/render cycle, productized (extends the prototype's most polished piece):**

- [ ] **Video player with annotation:** Spacebar workflow (pause → draw → speak → save → resume), drawing tools (freehand, rectangle, circle, arrow, text), speech-to-text input
- [ ] **AI analysis:** Send annotation context (frame, drawing, text, spec, source code) to Claude; return structured assessment with severity/category/fixes
- [ ] **Diff preview:** Show proposed code changes before applying. User can accept, reject, or edit.
- [ ] **AI fix:** Apply accepted changes to source files with git commit per fix (automatic rollback support)
- [ ] **Section re-render + re-stitch:** Re-render only the affected section, reassemble full video
- [ ] **Batch fixes:** Queue multiple annotations on the same section, apply all fixes, render once

### 9.3 Reliability (Must Have)

**P0 — Things that are currently broken or fragile:**

- [ ] **Project config:** Section registry, composition mappings, and pipeline settings in a config file (not hardcoded in `server.js`)
- [ ] **Database-backed persistence:** Replace `annotations.json` with SQLite or Postgres. Support concurrent access, annotation history, and backup.
- [ ] **Structured Claude output:** Use Claude's tool_use mode or structured output instead of free-form JSON parsing with three fallback strategies
- [ ] **Git integration:** Auto-commit before and after every Claude fix. Enable `git diff` preview and `git revert` for bad fixes.
- [ ] **Job retry:** Allow retrying failed jobs (any pipeline stage, not just resolve) without re-running upstream steps
- [ ] **Asset manifest:** Central registry of all clips, audio segments, reference images, and generated compositions — replacing the current scatter across `outputs/`, `remotion/public/`, and `references/`

### 9.4 Efficiency (Should Have)

**P1 — Performance and cost improvements:**

- [ ] **Incremental rendering:** Render only the frames around the fix (Remotion supports `--frames` flag), composite into existing section video
- [ ] **Claude session reuse:** Keep a warm Claude session per section instead of cold-starting the CLI for every invocation
- [ ] **Parallel pipeline stages:** Run independent pipeline stages concurrently (e.g., TTS and Veo generation in parallel; multi-section renders in parallel)
- [ ] **Cost dashboard:** Track and display Claude API, Veo, Imagen, and Lambda costs per stage and per session

### 9.5 Collaboration (Should Have)

**P1 — Multi-user support:**

- [ ] **User accounts:** Basic auth with roles (director, editor, viewer)
- [ ] **Shared state:** WebSocket-based real-time sync of annotations and pipeline status across clients
- [ ] **Comment threads:** Discussion on annotations before resolving
- [ ] **Assignment:** Assign annotations to team members or to AI

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

## Appendix B: Project Directory Structure

Any video project built with this system should follow this general layout:

```
{project}/
├── narrative/
│   ├── main_script.md            # Source script (human-written)
│   └── tts_script.md             # TTS-optimized script (Claude Code-generated)
│
├── specs/
│   └── {NN-section-name}/        # One directory per section
│       ├── segment_NN_*.md       # Per-shot visual specs
│       ├── AUDIT_*.md            # Per-spec audit results
│       └── prompts/              # Veo prompt files (optional)
│
├── remotion/
│   ├── src/remotion/
│   │   ├── Root.tsx              # Composition registrations
│   │   ├── {NN-ComponentName}/   # Individual animation compositions
│   │   └── {S0N-SectionName}/    # Section wrapper compositions
│   ├── public/                   # Static assets (WAVs, MP4s) for Remotion
│   ├── deploy.mjs                # AWS Lambda deployment (optional)
│   └── package.json
│
├── tools/
│   ├── tts/
│   │   ├── render_tts.py         # TTS rendering
│   │   └── sync_audio_pipeline.py # Section grouping + Whisper
│   ├── veo/
│   │   ├── generate_segments.py  # Video clip generation
│   │   ├── generate_references.py # Reference image generation
│   │   └── composite_segments.py # Split-screen compositing
│   └── generate_section_compositions.py  # Whisper → BEATS → Remotion
│
├── review-app/
│   ├── server.js                 # Express API
│   ├── public/                   # Editor UI (spacebar workflow)
│   └── data/                     # Annotations + thumbnails
│
├── outputs/
│   ├── full_video.mp4            # Final stitched video
│   ├── sections/                 # Per-section rendered videos
│   ├── tts/                      # Audio segments + timestamps
│   └── veo/                      # Generated video clips
│
├── references/                   # Character reference images for Veo
├── audits/                       # QA audit reports
├── models/                       # Local model weights (TTS, etc.)
├── docs/                         # Process documentation
└── archive/                      # Stale files preserved for reference
```

> **In the demo (`demos/3blue1brown/`):**
> - `narrative/` — 3 files including `tts_cold_open.md` (cold open excerpt)
> - `specs/` — 6 section dirs (`00-cold-open` through `05-compound`), ~150+ spec files
> - `remotion/src/remotion/` — 60 registered compositions (`01-ColdOpen/` through `51-SockMetaphorFinal/`), 7 section wrappers (`S00-ColdOpen/` through `S06-Closing/`)
> - `tools/veo/` — 9 generation scripts (section-specific, see Section 5.3)
> - `review-app/` — `server.js` (862 lines), 7 public JS modules, `server.test.js` (Jest)
> - `outputs/` — `full_video.mp4` (232MB), 7 section videos, 112 TTS segments
> - `docs/` — `RENDERING_METHODOLOGY.md` (354 lines), `audio-synced-animation-process.md`
