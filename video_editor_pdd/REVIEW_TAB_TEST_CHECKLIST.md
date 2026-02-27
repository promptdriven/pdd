# Review Tab Manual Test Checklist

**Reference:** `demos/3blue1brown/PRD.md` §4.2 (Spacebar Workflow), §4.1 (Annotation Model), §4.3 (Claude Integration)
**Components tested:** `VideoPlayer`, `AnnotationPanel`, `FixPreviewPanel`, `SseLogPanel`

---

## 1. Tab Navigation

- [x] **1.1** App loads on Pipeline tab by default
- [x] **1.2** Clicking "Review" tab switches to Review layout
- [x] **1.3** Active tab has white text + blue bottom border; inactive has gray text
- [x] **1.4** Switching to Review tab triggers annotation load (loading indicator appears)
- [x] **1.5** Switching back to Pipeline tab restores stage panel

---

## 2. Review Tab Layout

- [x] **2.1** Two-column layout: VideoPlayer takes ~2/3 width on left, AnnotationPanel takes ~1/3 on right
- [x] **2.2** Columns separated by border
- [x] **2.3** Layout fills full viewport height (no scrollbar on outer container)

---

## 3. VideoPlayer — Initial State

- [x] **3.1** Video element renders (even if src returns 404/no video yet)
- [x] **3.2** Status badge shows "Review" in top-left corner
- [x] **3.3** Active tool name shows "FREEHAND" by default in badge
- [x] **3.4** Mic indicator visible if speech recognition available (shows mic emoji + "off")
- [x] **3.5** Play/Pause button visible below video ("Play/Pause (K)")
- [x] **3.6** Time display shows "0:00 / 0:00" when no video loaded
- [x] **3.7** Keyboard shortcut hints visible: "D R C A T • Space = Annotate M = Mic"
- [x] **3.8** Progress bar (gray) visible below time display
- [x] **3.9** Five drawing tool buttons visible: FREEHAND, RECTANGLE, CIRCLE, ARROW, TEXT
- [x] **3.10** FREEHAND tool is highlighted (blue) by default
- [x] **3.11** Canvas overlay is NOT interactive (pointer-events: none) when not recording

---

## 4. VideoPlayer — Drawing Tool Selection (Button Click)

- [x] **4.1** Clicking FREEHAND button highlights it blue, badge shows "FREEHAND"
- [x] **4.2** Clicking RECTANGLE button highlights it blue, badge shows "RECTANGLE"
- [x] **4.3** Clicking CIRCLE button highlights it blue, badge shows "CIRCLE"
- [x] **4.4** Clicking ARROW button highlights it blue, badge shows "ARROW"
- [x] **4.5** Clicking TEXT button highlights it blue, badge shows "TEXT"
- [x] **4.6** Only one tool is highlighted at a time

---

## 5. VideoPlayer — Keyboard Shortcuts

- [x] **5.1** `D` key selects FREEHAND tool (badge updates)
- [x] **5.2** `R` key selects RECTANGLE tool (badge updates)
- [x] **5.3** `C` key selects CIRCLE tool (badge updates)
- [x] **5.4** `A` key selects ARROW tool (badge updates)
- [x] **5.5** `T` key selects TEXT tool (badge updates)
- [x] **5.6** `K` key toggles play/pause on video
- [x] **5.7** `F` key toggles fullscreen
- [x] **5.8** `M` key toggles mic mode (if speech available) — indicator updates
- [x] **5.9** `Arrow Left` seeks video backward 5s
- [x] **5.10** `Arrow Right` seeks video forward 5s
- [x] **5.11** `Space` (1st press) enters recording mode — badge shows "Recording" + red pulse dot, canvas becomes interactive
- [x] **5.12** `Space` (2nd press) exits recording mode — badge reverts to "Review", canvas pointer-events disabled
- [x] **5.13** `Ctrl+Z` undoes last stroke when in recording mode
- [x] **5.14** Keyboard shortcuts do NOT fire when focus is in an input/textarea *(confirmed via source code: VideoPlayer.tsx:349)*

---

## 6. VideoPlayer — Recording / Annotation Workflow (Spacebar)

- [x] **6.1** Space press pauses video if it was playing
- [x] **6.2** Recording mode shows transcript area at bottom ("Transcript: …")
- [x] **6.3** Canvas accepts pointer events when recording mode is active
- [x] **6.4** Can draw freehand on canvas during recording
- [x] **6.5** Can draw rectangle on canvas during recording
- [x] **6.6** Can draw circle on canvas during recording
- [x] **6.7** Can draw arrow on canvas during recording
- [x] **6.8** TEXT tool triggers window.prompt for annotation text on click
- [x] **6.9** Second Space press captures annotation and exits recording mode
- [x] **6.10** After capture: strokes cleared from canvas
- [x] **6.11** After capture: transcript cleared
- [x] **6.12** `onAnnotationCapture` is called with correct data (timestamp, text, drawingDataUrl, compositeDataUrl)

---

## 7. VideoPlayer — Progress Bar & Annotation Markers

- [x] **7.1** Progress bar fills (blue) proportional to current time / duration
- [x] **7.2** Annotation markers appear as yellow dots on timeline
- [x] **7.3** Clicking an annotation marker seeks video to that timestamp
- [x] **7.4** Marker position is proportional to timestamp / duration

---

## 8. AnnotationPanel — Empty State

- [x] **8.1** Header "Annotations" is visible
- [x] **8.2** "Apply 0 Fixes" button is disabled when no unresolved analyzed annotations
- [x] **8.3** "No annotations yet." placeholder shown in annotation list *(verified via patched fetch returning `{ annotations: [] }` — placeholder rendered correctly)*

---

## 9. AnnotationPanel — Annotation Cards (with mock/existing annotations)

- [x] **9.1** Annotations sorted by timestamp (ascending)
- [x] **9.2** Each card shows thumbnail image (or gray placeholder if no compositeDataUrl)
- [x] **9.3** Each card shows formatted timestamp (e.g., "0:10.0")
- [x] **9.4** Each card shows severity badge with correct color:
  - [x] **9.4a** `critical` → red badge
  - [x] **9.4b** `major` → orange badge *(confirmed via source code)*
  - [x] **9.4c** `minor` → yellow badge
  - [x] **9.4d** `pass` → green badge
  - [x] **9.4e** No analysis → "unknown" badge (white/transparent)
- [x] **9.5** Each card shows fix type badge (e.g., "Remotion Fix", "No Fix", "Not analyzed")
- [x] **9.6** Annotation text displayed (clipped to 2 lines)
- [x] **9.7** Analysis summary shown (clipped to 1 line) with tooltip on hover
- [x] **9.8** Resolved annotations show green "✓ Resolved" badge
- [x] **9.9** Resolved annotations have green border/background tint
- [x] **9.10** Unresolved annotations have default border/background
- [x] **9.11** Clicking a card header expands the card (shows expanded content)
- [x] **9.12** Clicking again collapses the card

---

## 10. AnnotationPanel — Expanded Card

- [x] **10.1** "Technical assessment" section visible with full text
- [x] **10.2** "Suggested fixes" section visible with list items
- [x] **10.3** If no suggested fixes: "None." shown
- [x] **10.4** If analysis pending: "No analysis available." shown in technical assessment
- [x] **10.5** "Mark Resolved" button shown for unresolved annotations
- [x] **10.6** Clicking "Mark Resolved" marks annotation as resolved (local state — green badge appears)
- [x] **10.7** After marking resolved, "Mark Resolved" button disappears
- [x] **10.8** "View Diff" button shown when fixCommitSha exists *(verified via patched annotation with fixCommitSha — button visible in expanded card)*
- [x] **10.9** Clicking "View Diff" fetches and shows diff panel *(diff panel appeared with commit SHA + diff content)*
- [x] **10.10** Clicking "Hide Diff" collapses diff panel *(panel collapsed, button reverted to "View Diff")*
- [x] **10.11** "Revert Fix" button shown when fixCommitSha exists *(button visible alongside "View Diff")*
- [x] **10.12** "Retry" button shown when resolveJob failed (job.status === 'error')
- [x] **10.13** Inline progress spinner shown when resolveJob is running *(verified via patched job returning `{ status: "running", progress: 42 }` — spinner + "running 42%" visible)*

---

## 11. AnnotationPanel — Apply Fixes Button

- [x] **11.1** "Apply N Fixes" shows correct count of unresolved analyzed annotations
- [x] **11.2** Button is disabled if 0 unresolved analyzed annotations
- [x] **11.3** Button is disabled if batch job already in progress
- [x] **11.4** Clicking "Apply N Fixes" opens FixPreviewPanel
- [x] **11.5** FixPreviewPanel closes without applying when "Close" is clicked

---

## 12. FixPreviewPanel

- [x] **12.1** Loading state shown while fetching previews (spinner + "Generating previews...")
- [x] **12.2** Error state shown if fetch fails (red error box) *(verified via patched fetch → 500 — red "Preview failed (500)" box appeared)*
- [x] **12.3** Empty state shown if no fixes to preview ("No fixes to preview.") *(verified via patched fetch returning `{ previews: [] }` — empty message rendered)*
- [x] **12.4** Preview cards shown for each annotation with a fix
- [x] **12.5** Each card shows fix type badge (color-coded: purple=remotion)
- [x] **12.6** Each card shows confidence % (e.g., "0% confidence" when undefined → fixed Bug 3)
- [x] **12.7** Each card shows preview text description *(verified via patched response with real preview text — description shown correctly)*
- [x] **12.8** Files modified list shown when present *(verified — "Files: src/compositions/ColdOpenSection.tsx" row visible)*
- [x] **12.9** "Show diff" link toggles inline diff viewer *(verified — "Show diff" expands, "Hide diff" collapses the pre block)*
- [x] **12.10** Diff viewer renders monospaced code block *(verified — dark `<pre>` block with monospace font visible)*
- [x] **12.11** All fixes are checked by default
- [x] **12.12** Unchecking a fix removes it from the count/apply set
- [x] **12.13** Count shows "N of M fixes selected" at bottom
- [x] **12.14** "Apply N Fixes" button at bottom is disabled when 0 selected
- [x] **12.15** Clicking "Apply N Fixes" closes panel and triggers batch resolve
- [x] **12.16** "Close" button closes panel without applying

---

## 13. Batch Resolve — SSE Log Panel

- [x] **13.1** After applying fixes, SSE log panel appears in AnnotationPanel
- [x] **13.2** Log shows jobId
- [x] **13.3** Log streams progress messages in real time
- [x] **13.4** Log remains visible after batch completes (user can review)
- [x] **13.5** On success: annotations refresh (resolved ones update) *(Bug fixed: `onDone` callback now calls `onBatchResolve(batchJobId!)` — structural test passes)*
- [x] **13.6** On error: log remains with error message

---

## 14. Edge Cases & Error Handling

- [x] **14.1** If `/api/project` returns error, Review tab still renders (no crash) *(verified via structural tests — try/catch prevents crash, `projectConfig=null` fallback works, Review tab renders independently)*
- [x] **14.2** If `/api/annotations` returns error, panel shows gracefully (no crash) *(verified via patched fetch → 500 — error caught, "No annotations yet." shown, no crash)*
- [x] **14.3** Video src 404 does not crash VideoPlayer
- [x] **14.4** Annotation with no analysis shows "Awaiting analysis…" as summary
- [x] **14.5** Very long annotation text does not overflow card layout
- [x] **14.6** Multiple rapid Space presses don't create duplicate annotations *(4 presses = 2 complete cycles = 2 distinct annotations, no duplicates)*

---

## Test Progress Summary

| Section | Total | Passed | Failed | N/A |
|---------|-------|--------|--------|-----|
| 1. Tab Navigation | 5 | 5 | 0 | 0 |
| 2. Layout | 3 | 3 | 0 | 0 |
| 3. VideoPlayer Initial | 11 | 11 | 0 | 0 |
| 4. Tool Selection Buttons | 6 | 6 | 0 | 0 |
| 5. Keyboard Shortcuts | 14 | 14 | 0 | 0 |
| 6. Recording Workflow | 12 | 12 | 0 | 0 |
| 7. Progress Bar & Markers | 4 | 4 | 0 | 0 |
| 8. Annotation Panel Empty | 3 | 3 | 0 | 0 |
| 9. Annotation Cards | 12 | 12 | 0 | 0 |
| 10. Expanded Card | 13 | 13 | 0 | 0 |
| 11. Apply Fixes Button | 5 | 5 | 0 | 0 |
| 12. FixPreviewPanel | 16 | 16 | 0 | 0 |
| 13. SSE Log Panel | 6 | 6 | 0 | 0 |
| 14. Edge Cases | 6 | 6 | 0 | 0 |
| **Total** | **116** | **116** | **0** | **0** |

---

## Bugs Found

### Bug 1: Drawing-only annotation silently fails (FIXED)
- **File:** `app/api/annotations/route.ts`
- **Root cause:** Validation required non-empty `text` field; drawings with no voice/text returned 400 silently.
- **Fix:** Changed validation to allow empty `text` when `drawingDataUrl` is present.
- **Test:** `tests/integration/api_project_script_annotations.test.ts` — "POST with empty text but drawingDataUrl creates annotation (drawing-only)"

### Bug 2: FixPreviewPanel crashes when `filesModified` is undefined (FIXED)
- **File:** `components/FixPreviewPanel.tsx:138`
- **Root cause:** `p.filesModified.length` crashes when API response omits `filesModified` field.
- **Fix:** Changed to `p.filesModified?.length` and `p.filesModified?.join(...)`. Marked interface field as optional.
- **Test:** `tests/test_fix_preview_panel.tsx` — "filesModified null-safety" suite (3 tests)

### Bug 3: FixPreviewPanel shows "NaN% confidence" (FIXED)
- **File:** `components/FixPreviewPanel.tsx`
- **Root cause:** `Math.round(p.confidence * 100)` produces NaN when `confidence` is undefined.
- **Fix:** Changed to `Math.round((p.confidence ?? 0) * 100)`.
- **Test:** `tests/test_fix_preview_panel.tsx` — "confidence NaN-safety" suite (2 tests)

---

## Tests Written (TDD)

| Test File | Tests Added | Bug Fixed |
|-----------|-------------|-----------|
| `tests/integration/api_project_script_annotations.test.ts` | 1 | Bug 1 |
| `tests/test_fix_preview_panel.tsx` | 8 (new file) | Bugs 2 & 3 |

**Total new tests:** 9 across 2 files. All 39 affected tests pass.

---

### Bug 4: Annotations don't refresh after batch resolve completes (FIXED)
- **File:** `components/AnnotationPanel.tsx`
- **Root cause:** `SseLogPanel onDone` callback was a no-op. `onBatchResolve` was called immediately on job creation (too early, before job completes), so annotations never reloaded after the SSE "done" event.
- **Fix:** Changed `onDone` from no-op to `onBatchResolve(batchJobId!)` so the parent reloads annotations when the job finishes.
- **Test:** `tests/test_annotation_panel.tsx` section 27 — "onDone callback calls onBatchResolve with batchJobId to refresh annotations"

---

## Tests Written (TDD) — Updated

| Test File | Tests Added | Item/Bug |
|-----------|-------------|----------|
| `tests/integration/api_project_script_annotations.test.ts` | 1 | Bug 1 |
| `tests/test_fix_preview_panel.tsx` | 8 (original) + 12 new | Bugs 2 & 3; items 12.2, 12.3, 12.7–12.10 |
| `tests/test_annotation_panel.tsx` | 14 new | Items 10.8–10.11, 10.13, 13.5 (Bug 4) |
| `tests/test_app_page.tsx` | 4 new | Items 14.1, 14.2 |

**Total new tests this session:** 30 across 3 files. All pass.
