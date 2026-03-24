# Audio-Visual Sync Data Model Analysis

**Date:** 2026-03-23
**Context:** The video editor pipeline has had recurring audio-visual desync bugs. This document analyzes the root causes, evaluates five candidate data models, and recommends a path forward.

---

## 1. The Sync Problem

The pipeline produces video by independently generating audio (TTS) and visuals (specs → Veo clips + Remotion components), then merging them at render time. The core challenge: **visuals must play at the right time relative to narration.** When they don't, the viewer sees a "split screen" visual while hearing narration about a "sock toss," or a title card appears 2 seconds after the narrator has moved on.

### 1.1 Root Causes (from bug fixes in this codebase)

| Bug | Commit | Root cause |
|-----|--------|-----------|
| Spec timestamps 3.5x too large (60s for 17s section) | `0c4f143` | Stage 6 read word timestamps from wrong path; Claude guessed from script heading "0:00 – 2:00" |
| Stage 8 linearly scaled all timestamps, distorting relative timing | `0c4f143` | Scaling couldn't distinguish audio-derived timestamps from script-heading guesses |
| Split screen ended after 4s instead of 11s | `67e036f` | Companion veo specs occupied independent timeline slots, splitting the parent's time |
| Split screen didn't span consecutive narrative beats | `31b18a4` | Claude treated each `**[VISUAL:]**` as a separate component; no persistent layout concept |
| Wrong Veo clip in split panel | `bcb9abf` | `clipId`/`leftClipId`/`rightClipId` not recognized by manifest media resolver |
| Component generated from scratch, ignoring spec entirely | `780508d` | `findSpecForComponent` couldn't find spec when component name had section prefix |

### 1.2 Common Thread

Every bug stems from the same structural issue: **audio timing and visual timing are independent artifacts that the pipeline tries to reconcile after the fact.** Each fix adds a new heuristic to bridge the gap — word timestamp injection, scaling tolerance, companion filtering, prompt instructions about persistent layouts. The heuristics accumulate but don't eliminate the root cause.

---

## 2. Current Model: Flat Siblings

### 2.1 Structure

```
Section
  ├── Audio: outputs/tts/{id}/concatenated.wav
  │   └── WordTimestamp[]: { word, start, end, segmentId }
  │
  ├── Specs: specs/{specDir}/*.md  (flat list, no hierarchy)
  │   ├── 01_split_screen_hook.md   **Timestamp:** 0:00 - 0:11
  │   ├── 02_developer_ai_edit.md   **Timestamp:** 0:00 - 0:11
  │   ├── 03_grandmother_darning.md **Timestamp:** 0:00 - 0:11
  │   ├── 04_zoom_out.md            **Timestamp:** 0:06 - 0:11
  │   └── 05_sock_toss.md           **Timestamp:** 0:11 - 0:14
  │
  └── Compositions: VISUAL_SEQUENCE in constants.ts
      └── Entry[]: { id, startFrame, endFrame }  ← derived from spec timestamps
```

Each spec independently declares its own `**Timestamp:**` field. Stage 8 parses these, scales them to fit the section's audio duration, and builds the VISUAL_SEQUENCE.

### 2.2 How Sync Works

1. Stage 6 (Claude) writes `**Timestamp:**` in each spec
2. Stage 8 parses timestamps from spec markdown
3. If timestamps exceed audio duration → linearly scale all timestamps
4. If timestamps overlap → sequentialize into back-to-back slots
5. Generate VISUAL_SEQUENCE with computed frame numbers

### 2.3 Pros

- **Decoupled stages.** Can re-run specs without re-running TTS, or re-run Veo without touching compositions.
- **Simple file layout.** Flat list of specs, flat list of audio segments, flat list of clips.
- **Parallel generation.** All specs for a section generated in one Claude call.
- **Easy to add/remove/reorder** individual specs without restructuring.
- **No migration needed.** This is what's implemented and shipping.

### 2.4 Cons

- **Sync is reconstructed, not intrinsic.** Every stage that consumes timing must re-derive and re-align it.
- **Timestamp provenance is lost.** Stage 8 can't tell if `0:11` came from audio alignment or was guessed from a script heading.
- **Companion relationships are implicit.** Split-screen companion clips look identical to standalone specs — need heuristic filtering.
- **Scaling distorts accurate timestamps.** If even one spec has a wrong timestamp, linear scaling distorts all of them.
- **Same timing data re-parsed in 4+ places:** specs route, composition-timing, section-timing, audit-timing.

---

## 3. Candidate Model A: Beat-Centric

### 3.1 Structure

```
Section
  └── Beat[]: the atomic sync unit
      ├── narrationSegments: ["cold_open_001", "cold_open_002"]
      ├── audioWindow: { start: 0.00, end: 5.50 }
      │
      └── Visual spec(s) for this beat
          ├── spec.md
          ├── children: [companion specs]
          └── media: veo clip or remotion component
```

Each beat owns both its narration and its visual. Timing flows from the beat's audio window to its visual.

### 3.2 Evaluation Against Hard Cases

**Persistent layout (split screen spans beats 1-3):**
Beat 1 owns segments 001-002 + the split screen. Beat 2 owns segment 003 + the zoom-out overlay. The split screen needs to persist through Beat 2.

Result: **Fails.** The split screen is in Beat 1 but must display during Beat 2. Requires a "visual extends beyond its beat" concept, which breaks the clean nesting that makes beats attractive.

**Visual-only elements (title card with no narration):**
Needs an empty beat with no narration segments and an explicit duration.

Result: **Awkward.** Beats are defined by narration — a narration-less beat is a degenerate case.

### 3.3 Pros

- Sync by construction within a single beat
- Children are structural (under parent beat)
- Eliminates timestamp authoring for beat-contained visuals

### 3.4 Cons

- Persistent layouts break the nesting model
- Must define beats before spec generation — constrains Claude's creative freedom
- Parallel spec generation gets harder (Claude needs per-beat context)
- Rigid 1:1 beat-to-narration mapping doesn't match actual video structure
- High migration cost (new data structure, new pipeline stage)

---

## 4. Candidate Model B: Computed Timestamps from Narration Sync

### 4.1 Structure

```
Section
  ├── Audio: WordTimestamp[]
  │
  └── Specs: (no **Timestamp:** field)
      └── Visual:
          └── ## Narration Sync
              > "If you use Cursor... you're getting really good at this."
```

Specs don't declare timestamps. A resolution step matches the `## Narration Sync` quoted text against word timestamps and computes the time window automatically.

### 4.2 Evaluation Against Hard Cases

**Persistent layout (split screen spans beats 1-3):**
The split screen's Narration Sync quotes segments 001-002 ("If you use Cursor... you're getting really good at this."). The computed window is 0:00 – 5:50.

Result: **Fails.** The split screen displays until 0:11 but its narration sync text only covers 0:00 – 5:50. The visual's display duration is longer than its narration trigger. A 5.5-second error.

**Visual-only elements (title card with no narration):**
No narration sync text to match against.

Result: **Cannot compute.** Falls back to... what? An explicit duration, which is just a timestamp by another name.

### 4.3 Pros

- Eliminates timestamp authoring entirely
- Timestamps are always audio-derived (when they can be computed)
- Simple concept — match text to word timestamps

### 4.4 Cons

- **Fatal flaw:** Display duration ≠ narration trigger duration for persistent layouts
- Cannot handle visual-only elements
- Narration sync text matching is fuzzy — could match wrong words
- Removes Claude's ability to express timing intent for edge cases

---

## 5. Candidate Model C: Script Visual Markers (Cue Points)

### 5.1 Structure

```
Section
  └── CuePoint[]: derived from **[VISUAL:]** markers in main_script.md
      ├── scriptMarker: "Split screen. LEFT: Developer..."
      ├── narrationText: "If you use Cursor..."  (text following the marker)
      ├── audioWindow: { start: 0.00, end: 5.50 }  (resolved from TTS)
      │
      └── Visual spec references
```

The human-authored `**[VISUAL:]**` markers in the script define cue points. After TTS, each cue point's narration text is resolved to an audio window. Specs reference cue points instead of declaring timestamps.

### 5.2 Evaluation Against Hard Cases

**Persistent layout (split screen spans cues 1-4):**
Cue 1: "Split screen..." → 0:00. Cue 4: "Hard cut to modern day..." → 11:46. The split starts at cue 1 and ends at cue 4.

Result: **Works if Claude authors `endsCue: 4`.** But this requires Claude to understand that the split persists until the hard cut — the same understanding required to write correct timestamps. The model doesn't eliminate the dependency on Claude's semantic understanding.

**Visual-only elements:**
A title card has its own `**[VISUAL:]**` marker in the script, so it has a cue point. But the cue's audio window is empty (no narration follows).

Result: **Partially works.** The cue defines the position but not the duration.

### 5.3 Pros

- Uses the script's own structure (human-authored, stable)
- Available before TTS (can prototype visuals early)
- Semantically meaningful (each marker is a directorial intent)

### 5.4 Cons

- Not all scripts have `**[VISUAL:]**` markers
- Markers are too fine-grained for some beats (multiple markers for one visual)
- Still requires Claude to express start/end cue references — same knowledge as timestamps
- Adds a cue extraction stage and a cue resolution step
- Markers aren't numbered in the script — need stable IDs

---

## 6. Candidate Model D: EDL (Edit Decision List)

### 6.1 Structure

```
Section
  ├── NarrationTrack: segments with word-level timing (immutable)
  ├── VisualCatalog: specs + generated media (unordered, no timing)
  └── EditDecisionList: the sync contract
      └── Entry[]:
          ├── timelineStart, timelineEnd (absolute section time)
          ├── visualRef → catalog entry
          ├── sourceIn, sourceOut (which part of the visual to use)
          └── layer (for overlapping visuals)
```

Borrows from professional NLE (Non-Linear Editor) architecture. Three fully decoupled tracks: narration, visuals, and an EDL that binds them.

### 6.2 Evaluation Against Hard Cases

**Persistent layout:** EDL entry spans 0:00 – 0:11 on layer 0. Zoom-out overlay is a separate entry on layer 1.

Result: **Works perfectly.** The EDL is a timeline, so any duration and layering is expressible.

**Visual-only elements:** EDL entry at 0:16 – 0:18 with no narration reference.

Result: **Works perfectly.**

### 6.3 Pros

- Maximum expressiveness — any timing, layering, or transition is representable
- Clean separation of concerns (content vs timing vs sync)
- Battle-tested model (used by Premiere, DaVinci, etc.)

### 6.4 Cons

- **Overengineered for an AI-driven pipeline.** Professional NLEs have EDLs because human editors manipulate them directly. In this system, the EDL would be generated by Claude or computed — negating the direct-manipulation benefit.
- High migration cost
- The EDL itself needs to be correct — same dependency on Claude's semantic understanding
- Adds significant complexity for a pipeline that has 6 segments and 8 visuals per section

---

## 7. Candidate Model E: Narration Segment References

### 7.1 Structure

```
Section
  ├── Audio: WordTimestamp[] with segmentIds
  │
  └── Specs:
      └── Visual:
          ├── **Narration Segments:** cold_open_001, cold_open_002, cold_open_003
          ├── **Timestamp:** 0:00 - 0:11  (computed from segments, for backward compat)
          ├── children: [02_developer_ai_edit, 03_grandmother_darning]
          ├── ## Narration Sync
          │   > "If you use Cursor... you're getting really good at this."
          └── (visual description, data points, etc.)
```

Each spec declares which narration segments it is on screen during. `**Timestamp:**` is computed from the segment windows, not authored by Claude. `children` is an explicit field, not inferred from data points.

### 7.2 How Sync Works

1. TTS generates audio with word-level timestamps grouped by segmentId
2. Stage 6 (Claude) writes `**Narration Segments:**` listing all segments the visual covers
3. Stage 8 resolves segments → looks up start/end times from word_timestamps.json
4. Timeline entry: start = min(segment starts), end = max(segment ends)
5. `**Timestamp:**` is written back as a computed field for backward compatibility
6. No scaling. No sequentialization heuristics for segment-resolved specs.

### 7.3 Evaluation Against Hard Cases

**Persistent layout (split screen spans segments 001-003):**
Claude writes `**Narration Segments:** cold_open_001, cold_open_002, cold_open_003`. The instruction is: "list ALL segments this visual is on screen during, not just the trigger segments." The script says "Split screen holds" during segment 003's narration, so Claude includes it.

Timeline: start = 0.00 (seg 001 start), end = 11.28 (seg 003 end). **Correct.**

**Overlay (zoom-out starts mid-segment 003):**
The zoom-out references segment cold_open_003. Timeline: 5.82 – 11.28. The actual desired start is ~6.0s (0.18s into the segment).

Result: **0.18s error.** Acceptable for most video production. If sub-segment precision is needed, an optional `startOffset` field can express it.

**Visual-only elements (title card with no narration):**
`**Narration Segments:**` is empty. Falls back to `**Timestamp:**` (authored by Claude for this case only) or to the previous visual's end time + explicit duration.

Result: **Works via fallback.** Only narration-less visuals need authored timestamps — the minority case.

**Companion handling:**
`children: [02_developer_ai_edit, 03_grandmother_darning]` is explicit in the spec. No heuristic inference from data points needed. Stage 8 excludes children from the timeline directly.

Result: **Works by construction.**

**TTS re-run:**
Segment IDs stay the same (they're derived from script structure, not audio timing). Segment time windows shift. Specs reference IDs, so they stay valid. `**Timestamp:**` is recomputed from the new segment windows.

Result: **Survives TTS re-runs without re-running specs.**

### 7.4 Pros

- **Sync by reference.** Timestamps are computed from audio ground truth, not guessed.
- **Persistent layouts work naturally.** Claude lists all segments the visual covers — the union gives the correct window.
- **Children are explicit.** No heuristic inference needed.
- **Backward compatible.** `**Timestamp:**` stays as computed output. Old specs without segments use timestamp fallback.
- **Incremental migration.** Add one field to spec format, update Stage 8 resolution logic.
- **Eliminates scaling heuristics.** Segment-resolved timestamps are already audio-accurate.
- **Survives TTS re-runs.** Segment IDs are stable references.
- **Claude is good at this task.** Matching "this visual accompanies these narration sentences" is a semantic task LLMs excel at, unlike arithmetic with timestamps.

### 7.5 Cons

- **Sub-segment precision is limited.** Visuals that start mid-segment have ~0.2s error. Solvable with optional `startOffset` but adds complexity.
- **Segment IDs are TTS implementation details.** If TTS processing changes how segments are defined (e.g., splitting long segments), references could break. Mitigated by re-running Stage 6 when TTS changes.
- **Narration-less visuals fall back to timestamps.** Title cards, transitions, and visual-only beats still need some form of explicit timing.
- **Claude must choose the right segments.** If Claude references segments 001-002 but should include 003, the visual is too short. Same knowledge dependency as timestamps — but the failure mode is "wrong segments listed" rather than "wrong number computed."
- **Two fields to maintain.** `**Narration Segments:**` (source of truth) and `**Timestamp:**` (computed) could drift if the computation step is skipped.

---

## 8. Comparative Matrix

| Dimension | Current (Flat) | A: Beats | B: Computed | C: Cue Points | D: EDL | **E: Segments** |
|-----------|---------------|----------|-------------|---------------|--------|----------------|
| Prevents wrong timestamps | No | Partially | Yes | Partially | Yes | **Yes** |
| Handles persistent layouts | No (heuristic) | No (breaks nesting) | No (fatal flaw) | Partially | Yes | **Yes** |
| Handles visual-only elements | Yes | Awkward | No | Partially | Yes | **Fallback** |
| Handles overlays | Via sequentialization | Needs extension | N/A | Needs extension | Yes | **Via segments** |
| Children explicit | No (inferred) | Yes | No | Yes | N/A | **Yes** |
| Survives TTS re-run | No | No | N/A | Yes | Depends | **Yes** |
| Claude's task difficulty | Hard (arithmetic) | Medium | N/A | Medium | Hard | **Easy (semantic)** |
| Migration cost | None | High | Medium | Medium | High | **Low** |
| Backward compatible | N/A | No | No | No | No | **Yes** |

---

## 9. Recommendation

**Three generated manifests: canonical narration + explicit visual contract + holistic section timeline.**

Model E's segment references are the right *primitive* — but they belong in generated manifests, not as new prose headers in markdown specs. This follows the codebase's existing direction toward generated manifests and structured contracts (commits `0404054e6`, `66211bb14`, `328bb2f9a`, `69057105a`).

### 9.1 The Three Manifests

#### Manifest 1: Canonical Narration (`outputs/tts/{sectionId}/segments.json`)

Single source of narration structure. Produced once by TTS/audio sync. Every word has a `segmentId`, every segment has `id`, `text`, `start`, `end`.

```json
{
  "sectionId": "cold_open",
  "duration": 17.54,
  "segments": [
    { "id": "cold_open_001", "text": "If you use cursor or Claude Code or...", "start": 0.00, "end": 2.72 },
    { "id": "cold_open_002", "text": "you're getting really good at this.", "start": 3.46, "end": 5.50 },
    { "id": "cold_open_003", "text": "Ah, but here's what your great-grandmother...", "start": 5.82, "end": 11.28 }
  ],
  "words": [
    { "word": "If", "start": 0.00, "end": 0.24, "segmentId": "cold_open_001" }
  ]
}
```

**Must be canonicalized first.** The Python TTS renderer (`scripts/render_tts.py:242`) and the TS segment parser (`lib/tts-segments.ts:59`) currently derive segments differently. Until there is one canonical parser and one canonical manifest, anything anchored to segment IDs is brittle.

#### Manifest 2: Visual Contract (`outputs/compositions/visual-manifest.json`)

Extends the existing `visual-manifest.json` with explicit structure fields. This is where identity, container/child relationships, and media aliases belong.

```json
{
  "id": "01_split_screen_hook",
  "specBaseName": "01_split_screen_hook",
  "renderMode": "component",
  "parentId": null,
  "children": ["02_developer_ai_edit", "03_grandmother_darning"],
  "mediaAliases": {
    "leftSrc": "veo/developer_ai_edit.mp4",
    "rightSrc": "veo/grandmother_darning.mp4"
  },
  "dataPoints": {
    "type": "split_screen",
    "coverSegments": ["cold_open_001", "cold_open_002", "cold_open_003"],
    "laneHint": 0
  }
}
```

- `parentId` / `children`: explicit container relationships (replaces heuristic inference from `collectEmbeddedCompanionIds`)
- `coverSegments`: timing hint from Claude in Data Points JSON (not a new markdown header)
- `laneHint`: overlay intent (0 = base, 1+ = overlay)

**`coverSegments` is a hint, not source of truth.** Claude provides it in `## Data Points JSON`. The generated timeline manifest is authoritative.

#### Manifest 3: Section Timeline (`outputs/compositions/section-timeline.json`)

Generated holistically by Stage 8 from the narration manifest + all visual contracts for the section. This is the authoritative timing contract that render, preview, audit, and subtitles all read.

```json
{
  "sectionId": "cold_open",
  "duration": 17.54,
  "entries": [
    {
      "id": "01_split_screen_hook",
      "lane": 0,
      "start": { "type": "segmentStart", "segmentId": "cold_open_001" },
      "end": { "type": "segmentEnd", "segmentId": "cold_open_003" },
      "resolvedStartSeconds": 0.00,
      "resolvedEndSeconds": 11.28,
      "source": "segment-anchor"
    },
    {
      "id": "04_zoom_out_accumulated",
      "lane": 1,
      "start": { "type": "segmentStart", "segmentId": "cold_open_003", "offsetMs": 180 },
      "end": { "type": "segmentEnd", "segmentId": "cold_open_003" },
      "resolvedStartSeconds": 6.00,
      "resolvedEndSeconds": 11.28,
      "source": "segment-anchor"
    },
    {
      "id": "05_sock_toss",
      "lane": 0,
      "start": { "type": "segmentStart", "segmentId": "cold_open_004" },
      "end": { "type": "segmentEnd", "segmentId": "cold_open_004" },
      "resolvedStartSeconds": 11.46,
      "resolvedEndSeconds": 13.94,
      "source": "segment-anchor"
    },
    {
      "id": "08_pdd_title_card",
      "lane": 0,
      "start": { "type": "absolute", "seconds": 16.0 },
      "end": { "type": "sectionEnd" },
      "resolvedStartSeconds": 16.0,
      "resolvedEndSeconds": 17.54,
      "source": "absolute"
    }
  ]
}
```

Supported anchor types: `segmentStart`, `segmentEnd`, `sectionStart`, `sectionEnd`, `absolute`. All anchors support optional `offsetMs` for sub-segment precision.

The `source` field preserves provenance: `segment-anchor` (resolved from segment references), `absolute` (explicit positioning for narration-less visuals), `timestamp-fallback` (legacy specs without segment data).

### 9.2 Generation Strategy

**Stage 6 (specs):** Keeps generating visual spec markdown. Emits timing hints in `## Data Points JSON` — specifically `coverSegments`, `children`, `laneHint`, and optional `startOffsetMs`/`endOffsetMs`. Does NOT add new markdown prose headers. `**Timestamp:**` remains as a backward-compatible display hint, no longer source of truth.

**Stage 8 (compositions) — holistic resolver:** Reads narration manifest + all visual contracts for the section. Resolution rules:

1. For each visual with `coverSegments`: resolve to segment windows, apply offsets
2. For each visual with `compositeOver` or `laneHint > 0`: assign to overlay lane
3. For each visual with `children`: exclude children from timeline (they render inside the parent)
4. For visuals without `coverSegments`: fall back to `**Timestamp:**` parsing (legacy path with existing heuristics)
5. Detect conflicts: two non-overlay visuals claiming the same segment without layering → warn
6. Detect gaps: time ranges with no visual → fill with fallback or warn
7. Write `section-timeline.json` with resolved entries

**Render, preview, audit:** Read `section-timeline.json` directly instead of reparsing spec timestamps. `VISUAL_SEQUENCE` in `constants.ts` is generated from the timeline manifest.

### 9.3 Why This Is the Right Model

| Criterion | Why it's satisfied |
|-----------|-------------------|
| Follows repo direction | Extends existing `visual-manifest.json` and composition manifests, consistent with commits moving toward generated contracts |
| Fixes the real failure pattern | Timing provenance (`source` field), container/child structure (`parentId`/`children`), and media identity (`mediaAliases`) — all three root causes addressed |
| Fits the runtime | The Remotion wrapper already supports concurrent `activeVisuals` via `VISUAL_SEQUENCE.filter()`. Lanes in the timeline let overlapping entries through instead of sequentializing them |
| Avoids extending the anti-pattern | No new prose headers in markdown specs. Timing hints go in `## Data Points JSON` (already parsed). Machine state lives in generated manifests under `outputs/` |
| Holistic resolution | Stage 8 sees ALL visuals at once — can detect gaps, overlaps, and container/child conflicts. Per-spec timestamp authoring can't do this |
| Backward compatible | Old specs without `coverSegments` fall back to `**Timestamp:**` parsing. Timeline entries get `source: "timestamp-fallback"` so downstream consumers know the provenance |

### 9.4 Migration Path

1. **Phase 1: Canonicalize narration segments.** Unify the Python (`scripts/render_tts.py:242`) and TS (`lib/tts-segments.ts:59`) segment parsers. Write `outputs/tts/{sectionId}/segments.json` as the canonical manifest. This is prerequisite infrastructure — everything else depends on stable segment IDs.

2. **Phase 2: Extend visual contract manifest.** Add `parentId`, `children`, and structured timing hints (`coverSegments`, `laneHint`) to `visual-manifest.json`. The manifest builder already parses Data Points JSON — extend it to extract these fields. Update the specs list API and audit stage to read `children` from the manifest instead of inferring from spec content.

3. **Phase 3: Generate section timeline manifest.** Implement the holistic resolver in Stage 8. Write `section-timeline.json` with lane and anchor entries. Generate `VISUAL_SEQUENCE` in `constants.ts` from the timeline manifest. Redirect render, preview, and audit to read the timeline manifest.

4. **Phase 4: Deprecate timestamp source-of-truth.** Stop reading `**Timestamp:**` as authoritative for specs that have `coverSegments`. Keep the field in specs as a human-readable display hint. Remove scaling/clamping heuristics for segment-resolved entries.

### 9.5 What This Eliminates

| Current code | Purpose | Status after migration |
|-------------|---------|----------------------|
| `scaleSpecCandidatesToSectionDuration` (15% tolerance) | Prevent scaling distortion | Eliminated for segment-resolved entries |
| `sequentializeTimings` | Spread overlapping timestamps | Replaced by lane-aware timeline generation |
| `collectEmbeddedCompanionIds` + `isEmbeddedCompanion` | Filter companions from timeline | Replaced by explicit `children` in visual contract |
| `resolveParentSpecs` / `extractChildClipIds` | Infer parent-child for UI | Replaced by explicit `parentId`/`children` in visual contract |
| `parseSpecTimestampRange` as timing source | Extract timing from spec markdown | Demoted to fallback for legacy specs only |
| Per-consumer manifest reparsing | Audit, render, preview each reparse specs | All read `section-timeline.json` |

### 9.6 Stage 8 Resolution Rules

The holistic resolver needs explicit rules, not just "resolve holistically." Concrete rules:

1. **Container extension:** If a visual has `children`, its timeline entry must fully contain all children's entries. If `coverSegments` doesn't cover a child, extend the parent's segments to include the child's.
2. **Lane assignment:** `laneHint: 0` (or absent) = base lane. `laneHint: 1+` or `compositeOver` present = overlay lane. Two base-lane visuals with overlapping resolved times = conflict (warn and sequentialize).
3. **Gap handling:** Time ranges between entries with no visual = implicit gap. If the section has audio during the gap, warn. Optionally fill with a fallback visual (e.g., the previous visual holds).
4. **Absolute positioning:** Visuals with no `coverSegments` and no `**Timestamp:**` = placed after the last resolved entry, with a default duration of 2 seconds.
5. **Fallback:** Specs without `coverSegments` in Data Points JSON use `**Timestamp:**` with all existing heuristics (scaling, clamping, sequentializing). Timeline entries get `source: "timestamp-fallback"`.

---

## 10. Why Not the Others

**Current flat model:** Sync is reconstructed from per-spec timestamps, not intrinsic. Every fix adds a new heuristic. The heuristics accumulate but don't eliminate the root cause.

**Model E (segment references in markdown):** Right primitive, wrong storage. Adding `**Narration Segments:**` and `**Children:**` as markdown headers extends the anti-pattern of prose specs as machine state. The codebase is already moving toward generated manifests — Model E moves against that direction.

**Beats (Model A):** The clean nesting breaks on persistent layouts — the most important case to get right. Adding "visual extends beyond beat" patches the nesting model but sacrifices the structural guarantee that makes beats attractive.

**Computed from Narration Sync (Model B):** Fatal flaw. Display duration ≠ narration trigger duration. The split screen is on screen for 11s but its narration sync text covers 5.5s. Cannot handle visual-only elements at all.

**Cue Points (Model C):** Requires numbered visual markers in the script (authoring burden) and Claude to author start/end cue references (same knowledge as timestamps). Adds complexity without clear benefit over segment references.

**Full EDL (Model D):** Maximum expressiveness but maximum complexity. Professional NLEs need EDLs for direct human manipulation. The three-manifest model provides the same separation of concerns (narration track, visual catalog, sync contract) in a form suited to AI-driven generation rather than human editing.

---

## 11. Open Questions

1. **Sub-segment precision.** The zoom-out starts 0.18s into segment 003. The `offsetMs` field in timeline anchors handles this. How often do visuals need sub-segment precision? If rare, `offsetMs` is a sufficient escape hatch. If common, segment granularity may need refinement.

2. **Segment stability across TTS engines.** If we switch from Qwen3-TTS to a different engine, will the canonical segment manifest produce the same IDs? Segment IDs should be derived from script structure (sentence boundaries), not TTS internals. The canonical parser should define segmentation rules explicitly.

3. **Claude's `coverSegments` accuracy.** Will Claude reliably include all segments for persistent layouts? The prompt instruction ("list ALL segments this visual is on screen during") combined with script visual beats gives sufficient context. The holistic resolver catches container/child inconsistencies. But wrong segments cannot be auto-corrected — only flagged.

4. **Timeline manifest invalidation.** When should the timeline manifest be regenerated? After any spec change (Stage 6 re-run), after TTS re-run, or only when explicitly triggered? Recommendation: regenerate as part of every Stage 8 run, since Stage 8 already reads all inputs.
