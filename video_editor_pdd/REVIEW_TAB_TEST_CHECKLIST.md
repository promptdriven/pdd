# Review Tab Manual Test Checklist

**Reference:** `demos/3blue1brown/PRD.md` §4.2 (Spacebar Workflow), §4.1 (Annotation Model), §4.3 (Claude Integration)
**Components tested:** `VideoPlayer`, `AnnotationPanel`, `FixPreviewPanel`, `SseLogPanel`

---

## 1. Tab Navigation

- [ ] **1.1** App loads on Pipeline tab by default
- [ ] **1.2** Clicking "Review" tab switches to Review layout
- [ ] **1.3** Active tab has white text + blue bottom border; inactive has gray text
- [ ] **1.4** Switching to Review tab triggers annotation load (loading indicator appears)
- [ ] **1.5** Switching back to Pipeline tab restores stage panel

---

## 2. Review Tab Layout

- [ ] **2.1** Two-column layout: VideoPlayer takes ~2/3 width on left, AnnotationPanel takes ~1/3 on right
- [ ] **2.2** Columns separated by border
- [ ] **2.3** Layout fills full viewport height (no scrollbar on outer container)

---

## 3. VideoPlayer — Initial State

- [ ] **3.1** Video element renders (even if src returns 404/no video yet)
- [ ] **3.2** Status badge shows "Review" in top-left corner
- [ ] **3.3** Active tool name shows "FREEHAND" by default in badge
- [ ] **3.4** Mic indicator visible if speech recognition available (shows mic emoji + "off")
- [ ] **3.5** Play/Pause button visible below video ("Play/Pause (K)")
- [ ] **3.6** Time display shows "0:00 / 0:00" when no video loaded
- [ ] **3.7** Keyboard shortcut hints visible: "D R C A T • Space = Annotate M = Mic"
- [ ] **3.8** Progress bar (gray) visible below time display
- [ ] **3.9** Five drawing tool buttons visible: FREEHAND, RECTANGLE, CIRCLE, ARROW, TEXT
- [ ] **3.10** FREEHAND tool is highlighted (blue) by default
- [ ] **3.11** Canvas overlay is NOT interactive (pointer-events: none) when not recording

---

## 4. VideoPlayer — Drawing Tool Selection (Button Click)

- [ ] **4.1** Clicking FREEHAND button highlights it blue, badge shows "FREEHAND"
- [ ] **4.2** Clicking RECTANGLE button highlights it blue, badge shows "RECTANGLE"
- [ ] **4.3** Clicking CIRCLE button highlights it blue, badge shows "CIRCLE"
- [ ] **4.4** Clicking ARROW button highlights it blue, badge shows "ARROW"
- [ ] **4.5** Clicking TEXT button highlights it blue, badge shows "TEXT"
- [ ] **4.6** Only one tool is highlighted at a time

---

## 5. VideoPlayer — Keyboard Shortcuts

- [ ] **5.1** `D` key selects FREEHAND tool (badge updates)
- [ ] **5.2** `R` key selects RECTANGLE tool (badge updates)
- [ ] **5.3** `C` key selects CIRCLE tool (badge updates)
- [ ] **5.4** `A` key selects ARROW tool (badge updates)
- [ ] **5.5** `T` key selects TEXT tool (badge updates)
- [ ] **5.6** `K` key toggles play/pause on video
- [ ] **5.7** `F` key toggles fullscreen
- [ ] **5.8** `M` key toggles mic mode (if speech available) — indicator updates
- [ ] **5.9** `Arrow Left` seeks video backward 5s
- [ ] **5.10** `Arrow Right` seeks video forward 5s
- [ ] **5.11** `Space` (1st press) enters recording mode — badge shows "Recording" + red pulse dot, canvas becomes interactive
- [ ] **5.12** `Space` (2nd press) exits recording mode — badge reverts to "Review", canvas pointer-events disabled
- [ ] **5.13** `Ctrl+Z` undoes last stroke when in recording mode
- [ ] **5.14** Keyboard shortcuts do NOT fire when focus is in an input/textarea

---

## 6. VideoPlayer — Recording / Annotation Workflow (Spacebar)

- [ ] **6.1** Space press pauses video if it was playing
- [ ] **6.2** Recording mode shows transcript area at bottom ("Transcript: …")
- [ ] **6.3** Canvas accepts pointer events when recording mode is active
- [ ] **6.4** Can draw freehand on canvas during recording
- [ ] **6.5** Can draw rectangle on canvas during recording
- [ ] **6.6** Can draw circle on canvas during recording
- [ ] **6.7** Can draw arrow on canvas during recording
- [ ] **6.8** TEXT tool triggers window.prompt for annotation text on click
- [ ] **6.9** Second Space press captures annotation and exits recording mode
- [ ] **6.10** After capture: strokes cleared from canvas
- [ ] **6.11** After capture: transcript cleared
- [ ] **6.12** `onAnnotationCapture` is called with correct data (timestamp, text, drawingDataUrl, compositeDataUrl)

---

## 7. VideoPlayer — Progress Bar & Annotation Markers

- [ ] **7.1** Progress bar fills (blue) proportional to current time / duration
- [ ] **7.2** Annotation markers appear as yellow dots on timeline
- [ ] **7.3** Clicking an annotation marker seeks video to that timestamp
- [ ] **7.4** Marker position is proportional to timestamp / duration

---

## 8. AnnotationPanel — Empty State

- [ ] **8.1** Header "Annotations" is visible
- [ ] **8.2** "Apply 0 Fixes" button is disabled when no annotations
- [ ] **8.3** "No annotations yet." placeholder shown in annotation list

---

## 9. AnnotationPanel — Annotation Cards (with mock/existing annotations)

- [ ] **9.1** Annotations sorted by timestamp (ascending)
- [ ] **9.2** Each card shows thumbnail image (or gray placeholder if no compositeDataUrl)
- [ ] **9.3** Each card shows formatted timestamp (e.g., "0:05.0")
- [ ] **9.4** Each card shows severity badge with correct color:
  - [ ] **9.4a** `critical` → red badge
  - [ ] **9.4b** `major` → orange badge
  - [ ] **9.4c** `minor` → yellow badge
  - [ ] **9.4d** `pass` → green badge
  - [ ] **9.4e** No analysis → "unknown" badge (white/transparent)
- [ ] **9.5** Each card shows fix type badge (e.g., "Remotion Fix", "Veo Regen", "TTS Re-render", "No Fix", "Not analyzed")
- [ ] **9.6** Annotation text displayed (clipped to 2 lines)
- [ ] **9.7** Analysis summary shown (clipped to 1 line) with tooltip on hover
- [ ] **9.8** Resolved annotations show green "✓ Resolved" badge
- [ ] **9.9** Resolved annotations have green border/background tint
- [ ] **9.10** Unresolved annotations have default border/background
- [ ] **9.11** Clicking a card header expands the card (shows expanded content)
- [ ] **9.12** Clicking again collapses the card

---

## 10. AnnotationPanel — Expanded Card

- [ ] **10.1** "Technical assessment" section visible with full text
- [ ] **10.2** "Suggested fixes" section visible with list items
- [ ] **10.3** If no suggested fixes: "None." shown
- [ ] **10.4** If analysis pending: "No analysis available." shown in technical assessment
- [ ] **10.5** "Mark Resolved" button shown for unresolved annotations
- [ ] **10.6** Clicking "Mark Resolved" marks annotation as resolved (local state — green badge appears)
- [ ] **10.7** After marking resolved, "Mark Resolved" button disappears
- [ ] **10.8** "View Diff" button shown when fixCommitSha exists
- [ ] **10.9** Clicking "View Diff" fetches and shows diff panel
- [ ] **10.10** Clicking "Hide Diff" collapses diff panel
- [ ] **10.11** "Revert Fix" button shown when fixCommitSha exists
- [ ] **10.12** "Retry" button shown when resolveJob failed (job.status === 'error')
- [ ] **10.13** Inline progress spinner shown when resolveJob is running

---

## 11. AnnotationPanel — Apply Fixes Button

- [ ] **11.1** "Apply N Fixes" shows correct count of unresolved analyzed annotations
- [ ] **11.2** Button is disabled if 0 unresolved analyzed annotations
- [ ] **11.3** Button is disabled if batch job already in progress
- [ ] **11.4** Clicking "Apply N Fixes" opens FixPreviewPanel
- [ ] **11.5** FixPreviewPanel closes without applying when "Close" is clicked

---

## 12. FixPreviewPanel

- [ ] **12.1** Loading state shown while fetching previews (spinner + "Generating previews...")
- [ ] **12.2** Error state shown if fetch fails (red error box)
- [ ] **12.3** Empty state shown if no fixes to preview ("No fixes to preview.")
- [ ] **12.4** Preview cards shown for each annotation with a fix
- [ ] **12.5** Each card shows fix type badge (color-coded: purple=remotion, cyan=veo, amber=tts)
- [ ] **12.6** Each card shows confidence % (e.g., "85% confidence")
- [ ] **12.7** Each card shows preview text description
- [ ] **12.8** Files modified list shown when present
- [ ] **12.9** "Show diff" link toggles inline diff viewer
- [ ] **12.10** Diff viewer renders monospaced code block
- [ ] **12.11** All fixes are checked by default
- [ ] **12.12** Unchecking a fix removes it from the count/apply set
- [ ] **12.13** Count shows "N of M fixes selected" at bottom
- [ ] **12.14** "Apply N Fixes" button at bottom is disabled when 0 selected
- [ ] **12.15** Clicking "Apply N Fixes" closes panel and triggers batch resolve
- [ ] **12.16** "Close" button closes panel without applying

---

## 13. Batch Resolve — SSE Log Panel

- [ ] **13.1** After applying fixes, SSE log panel appears in AnnotationPanel
- [ ] **13.2** Log shows jobId
- [ ] **13.3** Log streams progress messages in real time
- [ ] **13.4** Log remains visible after batch completes (user can review)
- [ ] **13.5** On success: annotations refresh (resolved ones update)
- [ ] **13.6** On error: log remains with error message

---

## 14. Edge Cases & Error Handling

- [ ] **14.1** If `/api/project` returns error, Review tab still renders (no crash)
- [ ] **14.2** If `/api/annotations` returns error, panel shows gracefully (no crash)
- [ ] **14.3** Video src 404 does not crash VideoPlayer
- [ ] **14.4** Annotation with no analysis shows "Awaiting analysis…" as summary
- [ ] **14.5** Very long annotation text does not overflow card layout
- [ ] **14.6** Multiple rapid Space presses don't create duplicate annotations

---

## Test Progress Summary

| Section | Total | Passed | Failed | Blocked |
|---------|-------|--------|--------|---------|
| 1. Tab Navigation | 5 | 0 | 0 | 0 |
| 2. Layout | 3 | 0 | 0 | 0 |
| 3. VideoPlayer Initial | 11 | 0 | 0 | 0 |
| 4. Tool Selection Buttons | 6 | 0 | 0 | 0 |
| 5. Keyboard Shortcuts | 14 | 0 | 0 | 0 |
| 6. Recording Workflow | 12 | 0 | 0 | 0 |
| 7. Progress Bar & Markers | 4 | 0 | 0 | 0 |
| 8. Annotation Panel Empty | 3 | 0 | 0 | 0 |
| 9. Annotation Cards | 12 | 0 | 0 | 0 |
| 10. Expanded Card | 13 | 0 | 0 | 0 |
| 11. Apply Fixes Button | 5 | 0 | 0 | 0 |
| 12. FixPreviewPanel | 16 | 0 | 0 | 0 |
| 13. SSE Log Panel | 6 | 0 | 0 | 0 |
| 14. Edge Cases | 6 | 0 | 0 | 0 |
| **Total** | **116** | **0** | **0** | **0** |

---

## Bugs Found

_None yet._

---

## Tests Written (TDD)

_None yet._
