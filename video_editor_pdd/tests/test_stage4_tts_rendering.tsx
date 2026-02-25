/**
 * Tests for components/stages/Stage4TtsRendering.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage4_tts_rendering_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Toolbar: [Render All] and [Render Missing] buttons triggering POST /api/pipeline/tts-render/run.
 *   3. Segment table columns: #, segment ID, status badge (done/missing/error), [▶] play, [↺] re-render.
 *   4. Row expansion on click: WaveSurfer.js waveform and raw TTS text.
 *   5. Batch progress bar: current segment ID and overall percent.
 *   6. Per-row [↺] re-render: POST with { segments: [segmentId] }, inline SseLogPanel.
 *   7. Load segments: GET /api/pipeline/tts-render/segments on mount and after each render.
 *   8. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage4TtsRendering.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive (Req 8)
// ---------------------------------------------------------------------------

describe("'use client' directive", () => {
  it("has 'use client' as the very first line", () => {
    const firstLine = sourceCode.split("\n")[0].trim();
    expect(firstLine).toBe("'use client';");
  });
});

// ---------------------------------------------------------------------------
// 2. Module structure
// ---------------------------------------------------------------------------

describe("module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("is a TypeScript React file", () => {
    expect(SOURCE_PATH).toMatch(/\.tsx$/);
  });

  it("exports Stage4TtsRendering as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+Stage4TtsRendering/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage4TtsRendering props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage4TtsRenderingProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage4TtsRenderingProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}\s*:\s*Stage4TtsRenderingProps/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React and hooks from react", () => {
    expect(sourceCode).toMatch(/import\s+React/);
    expect(sourceCode).toMatch(/from\s+['"]react['"]/);
  });

  it("imports useState from react", () => {
    expect(sourceCode).toMatch(/useState/);
  });

  it("imports useEffect from react", () => {
    expect(sourceCode).toMatch(/useEffect/);
  });

  it("imports useCallback from react", () => {
    expect(sourceCode).toMatch(/useCallback/);
  });

  it("imports useMemo from react", () => {
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("imports useRef from react", () => {
    expect(sourceCode).toMatch(/useRef/);
  });

  it("imports WaveSurfer from wavesurfer.js", () => {
    expect(sourceCode).toMatch(/import\s+WaveSurfer\s+from\s+['"]wavesurfer\.js['"]/);
  });

  it("imports SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s*\{?\s*SseLogPanel\s*\}?\s*from/);
  });
});

// ---------------------------------------------------------------------------
// 5. Type definitions
// ---------------------------------------------------------------------------

describe("type definitions", () => {
  it("defines SegmentStatus type as union of done | missing | error", () => {
    expect(sourceCode).toMatch(/type\s+SegmentStatus\s*=\s*['"]done['"]\s*\|\s*['"]missing['"]\s*\|\s*['"]error['"]/);
  });

  it("defines TtsSegment interface", () => {
    expect(sourceCode).toMatch(/interface\s+TtsSegment/);
  });

  it("TtsSegment has id: string property", () => {
    expect(sourceCode).toMatch(/id\s*:\s*string/);
  });

  it("TtsSegment has status: SegmentStatus property", () => {
    expect(sourceCode).toMatch(/status\s*:\s*SegmentStatus/);
  });

  it("TtsSegment has text: string property", () => {
    expect(sourceCode).toMatch(/text\s*:\s*string/);
  });

  it("defines BatchProgress interface", () => {
    expect(sourceCode).toMatch(/interface\s+BatchProgress/);
  });

  it("BatchProgress has currentSegment: string | null", () => {
    expect(sourceCode).toMatch(/currentSegment\s*:\s*string\s*\|\s*null/);
  });

  it("BatchProgress has completedCount: number", () => {
    expect(sourceCode).toMatch(/completedCount\s*:\s*number/);
  });

  it("BatchProgress has total: number", () => {
    expect(sourceCode).toMatch(/total\s*:\s*number/);
  });

  it("BatchProgress has percent: number", () => {
    expect(sourceCode).toMatch(/percent\s*:\s*number/);
  });
});

// ---------------------------------------------------------------------------
// 6. State management
// ---------------------------------------------------------------------------

describe("state management", () => {
  it("tracks segments state as TtsSegment[]", () => {
    expect(sourceCode).toMatch(/\[\s*segments\s*,\s*setSegments\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*TtsSegment\[\]\s*>\s*\(\s*\[\]\s*\)/);
  });

  it("tracks loading state as boolean", () => {
    expect(sourceCode).toMatch(/\[\s*loading\s*,\s*setLoading\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*boolean\s*>\s*\(\s*true\s*\)/);
  });

  it("tracks error state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*error\s*,\s*setError\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });

  it("tracks expandedId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*expandedId\s*,\s*setExpandedId\s*\]/);
  });

  it("tracks batchJobId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*batchJobId\s*,\s*setBatchJobId\s*\]/);
  });

  it("tracks batchProgress state as BatchProgress", () => {
    expect(sourceCode).toMatch(/\[\s*batchProgress\s*,\s*setBatchProgress\s*\]/);
  });

  it("tracks rowJobIds state as Record<string, string | null>", () => {
    expect(sourceCode).toMatch(/\[\s*rowJobIds\s*,\s*setRowJobIds\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 7. Ref management (Req 4 — WaveSurfer caching)
// ---------------------------------------------------------------------------

describe("ref management", () => {
  it("stores waveform container refs in a Map", () => {
    expect(sourceCode).toMatch(/waveformRefs\s*=\s*useRef\s*<\s*Map\s*<\s*string\s*,\s*HTMLDivElement\s*\|\s*null\s*>\s*>/);
  });

  it("stores WaveSurfer instances in a useRef<Map<string, WaveSurfer>>", () => {
    expect(sourceCode).toMatch(/wavesurferMap\s*=\s*useRef\s*<\s*Map\s*<\s*string\s*,\s*WaveSurfer\s*>\s*>/);
  });

  it("stores batch EventSource in a ref", () => {
    expect(sourceCode).toMatch(/batchEventSource\s*=\s*useRef\s*<\s*EventSource\s*\|\s*null\s*>/);
  });
});

// ---------------------------------------------------------------------------
// 8. allDone computation via useMemo (Req — Advance button)
// ---------------------------------------------------------------------------

describe("allDone computation", () => {
  it("uses useMemo for allDone", () => {
    expect(sourceCode).toMatch(/const\s+allDone\s*=\s*useMemo/);
  });

  it("checks that all segments have status done", () => {
    expect(sourceCode).toMatch(/segments\.every\s*\(\s*\(s\)\s*=>\s*s\.status\s*===\s*['"]done['"]\s*\)/);
  });

  it("requires segments.length > 0", () => {
    expect(sourceCode).toMatch(/segments\.length\s*>\s*0/);
  });

  it("depends on segments state", () => {
    expect(sourceCode).toMatch(/\[\s*segments\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 9. Segment fetching on mount (Req 7)
// ---------------------------------------------------------------------------

describe("segment fetching on mount", () => {
  it("fetches segments from GET /api/pipeline/tts-render/segments", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/tts-render\/segments['"]\s*\)/);
  });

  it("defines fetchSegments as useCallback", () => {
    expect(sourceCode).toMatch(/const\s+fetchSegments\s*=\s*useCallback/);
  });

  it("calls fetchSegments on mount via useEffect", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?fetchSegments\s*\(\s*\)/);
  });

  it("checks res.ok before parsing", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*throw/);
  });

  it("parses response as JSON", () => {
    expect(sourceCode).toMatch(/res\.json\s*\(\s*\)/);
  });

  it("sets loading to true at start", () => {
    expect(sourceCode).toMatch(/setLoading\s*\(\s*true\s*\)/);
  });

  it("sets loading to false in finally block", () => {
    expect(sourceCode).toMatch(/finally\s*\{[\s\S]*?setLoading\s*\(\s*false\s*\)/);
  });

  it("sets error on fetch failure", () => {
    expect(sourceCode).toMatch(/setError\s*\(\s*err\.message/);
  });
});

// ---------------------------------------------------------------------------
// 10. WaveSurfer initialization on row expand (Req 4)
// ---------------------------------------------------------------------------

describe("WaveSurfer initialization on expand", () => {
  it("initializes WaveSurfer only when expandedId changes", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?expandedId[\s\S]*?WaveSurfer\.create/);
  });

  it("skips initialization if no expandedId", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!expandedId\s*\)\s*return/);
  });

  it("skips initialization if WaveSurfer already exists for segment", () => {
    expect(sourceCode).toMatch(/wavesurferMap\.current\.has\s*\(\s*expandedId\s*\)/);
  });

  it("gets container from waveformRefs", () => {
    expect(sourceCode).toMatch(/waveformRefs\.current\.get\s*\(\s*expandedId\s*\)/);
  });

  it("creates WaveSurfer with correct container and url", () => {
    expect(sourceCode).toMatch(/WaveSurfer\.create\s*\(\s*\{/);
    expect(sourceCode).toMatch(/container/);
    expect(sourceCode).toMatch(/url\s*:\s*`\/api\/audio\/\$\{expandedId\}\.wav`/);
  });

  it("sets WaveSurfer height to 64", () => {
    expect(sourceCode).toMatch(/height\s*:\s*64/);
  });

  it("sets waveColor to #4ade80", () => {
    expect(sourceCode).toMatch(/waveColor\s*:\s*['"]#4ade80['"]/);
  });

  it("sets progressColor to #166534", () => {
    expect(sourceCode).toMatch(/progressColor\s*:\s*['"]#166534['"]/);
  });

  it("stores WaveSurfer instance in wavesurferMap", () => {
    expect(sourceCode).toMatch(/wavesurferMap\.current\.set\s*\(\s*expandedId\s*,\s*ws\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 11. Cleanup on unmount
// ---------------------------------------------------------------------------

describe("cleanup on unmount", () => {
  it("closes batch EventSource on unmount", () => {
    expect(sourceCode).toMatch(/batchEventSource\.current\?\.close\s*\(\s*\)/);
  });

  it("destroys all WaveSurfer instances on unmount", () => {
    expect(sourceCode).toMatch(/wavesurferMap\.current\.forEach\s*\(\s*\(ws\)\s*=>\s*ws\.destroy\s*\(\s*\)\s*\)/);
  });

  it("clears wavesurferMap on unmount", () => {
    expect(sourceCode).toMatch(/wavesurferMap\.current\.clear\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 12. Play button handler (Req 3 — ▶ play)
// ---------------------------------------------------------------------------

describe("play button handler", () => {
  it("defines handlePlay function", () => {
    expect(sourceCode).toMatch(/const\s+handlePlay\s*=/);
  });

  it("calls playPause on the WaveSurfer instance", () => {
    expect(sourceCode).toMatch(/ws\.playPause\s*\(\s*\)/);
  });

  it("retrieves WaveSurfer from wavesurferMap by id", () => {
    expect(sourceCode).toMatch(/wavesurferMap\.current\.get\s*\(\s*id\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Row toggle handler (Req 4 — expansion on click)
// ---------------------------------------------------------------------------

describe("row toggle handler", () => {
  it("defines handleRowToggle function", () => {
    expect(sourceCode).toMatch(/const\s+handleRowToggle\s*=/);
  });

  it("toggles expandedId between the clicked id and null", () => {
    expect(sourceCode).toMatch(/setExpandedId\s*\(\s*\(prev\)\s*=>\s*\(\s*prev\s*===\s*id\s*\?\s*null\s*:\s*id\s*\)\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Batch render — startBatchRender (Req 2)
// ---------------------------------------------------------------------------

describe("batch render", () => {
  it("defines startBatchRender as async function", () => {
    expect(sourceCode).toMatch(/const\s+startBatchRender\s*=\s*async/);
  });

  it("POSTs to /api/pipeline/tts-render/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/tts-render\/run['"]\s*,/);
  });

  it("uses POST method", () => {
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("sends Content-Type: application/json header", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]application\/json['"]/);
  });

  it("sends segments filter in body when provided", () => {
    expect(sourceCode).toMatch(/JSON\.stringify\s*\(\s*\{\s*segments\s*:\s*segmentsFilter\s*\}\s*\)/);
  });

  it("sends undefined body when no segments filter", () => {
    expect(sourceCode).toMatch(/segmentsFilter\s*\?\s*JSON\.stringify.*:\s*undefined/);
  });

  it("extracts jobId from response", () => {
    expect(sourceCode).toMatch(/data\.jobId/);
    expect(sourceCode).toMatch(/setBatchJobId\s*\(\s*jobId\s*\)/);
  });

  it("opens EventSource for SSE stream", () => {
    expect(sourceCode).toMatch(/new\s+EventSource\s*\(\s*`\/api\/jobs\/\$\{jobId\}\/stream`\s*\)/);
  });

  it("closes previous EventSource before opening new one", () => {
    expect(sourceCode).toMatch(/batchEventSource\.current\?\.close\s*\(\s*\)/);
  });

  it("resets batch progress before starting", () => {
    expect(sourceCode).toMatch(/setBatchProgress\s*\(\s*defaultProgress\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 15. SSE event handling for batch progress (Req 5)
// ---------------------------------------------------------------------------

describe("SSE event handling", () => {
  it("listens for 'message' events on EventSource", () => {
    expect(sourceCode).toMatch(/es\.addEventListener\s*\(\s*['"]message['"]/);
  });

  it("parses event data as JSON", () => {
    expect(sourceCode).toMatch(/JSON\.parse\s*\(\s*event\.data\s*\)/);
  });

  it("checks for payload.type === 'segment'", () => {
    expect(sourceCode).toMatch(/payload\.type\s*===\s*['"]segment['"]/);
  });

  it("updates segment status from SSE event", () => {
    expect(sourceCode).toMatch(/s\.id\s*===\s*payload\.segmentId/);
    expect(sourceCode).toMatch(/status\s*:\s*payload\.status\s+as\s+SegmentStatus/);
  });

  it("updates batch progress from SSE event", () => {
    expect(sourceCode).toMatch(/setBatchProgress/);
    expect(sourceCode).toMatch(/payload\.completedCount/);
    expect(sourceCode).toMatch(/payload\.total/);
  });

  it("calculates percent from completed and total", () => {
    expect(sourceCode).toMatch(/Math\.round\s*\(\s*\(\s*completed\s*\/\s*total\s*\)\s*\*\s*100\s*\)/);
  });

  it("listens for 'done' event", () => {
    expect(sourceCode).toMatch(/es\.addEventListener\s*\(\s*['"]done['"]/);
  });

  it("closes EventSource and clears batchJobId on done", () => {
    expect(sourceCode).toMatch(/['"]done['"][\s\S]*?batchEventSource\.current\?\.close/);
    expect(sourceCode).toMatch(/setBatchJobId\s*\(\s*null\s*\)/);
  });

  it("re-fetches segments after batch done", () => {
    expect(sourceCode).toMatch(/['"]done['"][\s\S]*?fetchSegments\s*\(\s*\)/);
  });

  it("listens for 'error' event", () => {
    expect(sourceCode).toMatch(/es\.addEventListener\s*\(\s*['"]error['"]/);
  });
});

// ---------------------------------------------------------------------------
// 16. Render All and Render Missing handlers (Req 2)
// ---------------------------------------------------------------------------

describe("Render All and Render Missing handlers", () => {
  it("defines handleRenderAll that calls startBatchRender with no args", () => {
    expect(sourceCode).toMatch(/const\s+handleRenderAll\s*=\s*\(\)\s*=>\s*startBatchRender\s*\(\s*\)/);
  });

  it("defines handleRenderMissing that filters non-done segments", () => {
    expect(sourceCode).toMatch(/const\s+handleRenderMissing\s*=/);
    expect(sourceCode).toMatch(/segments\.filter\s*\(\s*\(s\)\s*=>\s*s\.status\s*!==\s*['"]done['"]\s*\)/);
  });

  it("maps filtered segments to their IDs", () => {
    expect(sourceCode).toMatch(/\.map\s*\(\s*\(s\)\s*=>\s*s\.id\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 17. Per-row re-render handler (Req 6)
// ---------------------------------------------------------------------------

describe("per-row re-render handler", () => {
  it("defines handleRowRerender as async function", () => {
    expect(sourceCode).toMatch(/const\s+handleRowRerender\s*=\s*async/);
  });

  it("POSTs to /api/pipeline/tts-render/run with single segment", () => {
    expect(sourceCode).toMatch(/JSON\.stringify\s*\(\s*\{\s*segments\s*:\s*\[\s*segmentId\s*\]\s*\}\s*\)/);
  });

  it("stores jobId in rowJobIds for the segment", () => {
    expect(sourceCode).toMatch(/setRowJobIds\s*\(\s*\(prev\)\s*=>\s*\(\s*\{\s*\.\.\.prev\s*,\s*\[segmentId\]\s*:\s*jobId\s*\}\s*\)\s*\)/);
  });

  it("handles error on failure", () => {
    expect(sourceCode).toMatch(/handleRowRerender[\s\S]*?catch[\s\S]*?setError/);
  });
});

// ---------------------------------------------------------------------------
// 18. Status badge rendering (Req 3)
// ---------------------------------------------------------------------------

describe("status badge rendering", () => {
  it("defines renderStatusBadge function", () => {
    expect(sourceCode).toMatch(/const\s+renderStatusBadge\s*=/);
  });

  it("renders green badge for done status", () => {
    expect(sourceCode).toMatch(/bg-green-900\/50\s+text-green-400/);
    expect(sourceCode).toMatch(/>done</);
  });

  it("renders red badge for error status", () => {
    expect(sourceCode).toMatch(/bg-red-900\/50\s+text-red-400/);
    expect(sourceCode).toMatch(/>error</);
  });

  it("renders yellow badge for missing status", () => {
    expect(sourceCode).toMatch(/bg-yellow-900\/50\s+text-yellow-400/);
    expect(sourceCode).toMatch(/>missing</);
  });

  it("uses consistent badge base styling", () => {
    expect(sourceCode).toMatch(/px-2\s+py-1\s+text-xs\s+rounded\s+font-semibold/);
  });
});

// ---------------------------------------------------------------------------
// 19. Toolbar buttons (Req 2)
// ---------------------------------------------------------------------------

describe("toolbar buttons", () => {
  it("renders Render All button text", () => {
    expect(sourceCode).toMatch(/Render All/);
  });

  it("Render All button has onClick={handleRenderAll}", () => {
    expect(sourceCode).toMatch(/onClick=\{handleRenderAll\}/);
  });

  it("renders Render Missing button text", () => {
    expect(sourceCode).toMatch(/Render Missing/);
  });

  it("Render Missing button has onClick={handleRenderMissing}", () => {
    expect(sourceCode).toMatch(/onClick=\{handleRenderMissing\}/);
  });

  it("Render All button uses blue styling", () => {
    expect(sourceCode).toMatch(/bg-blue-600\s+text-white/);
  });
});

// ---------------------------------------------------------------------------
// 20. Advance button (Req — enabled when all segments done)
// ---------------------------------------------------------------------------

describe("Advance button", () => {
  it("renders Advance → button text", () => {
    expect(sourceCode).toMatch(/Advance →/);
  });

  it("button calls onAdvance on click", () => {
    expect(sourceCode).toMatch(/onClick=\{onAdvance\}/);
  });

  it("button is disabled when not all segments are done", () => {
    expect(sourceCode).toMatch(/disabled=\{!allDone\}/);
  });

  it("button has enabled styling when allDone is true", () => {
    expect(sourceCode).toMatch(/bg-emerald-600\s+text-white\s+hover:bg-emerald-700/);
  });

  it("button has disabled styling when allDone is false", () => {
    expect(sourceCode).toMatch(/bg-slate-700\s+text-slate-500/);
  });

  it("conditionally applies styling based on allDone", () => {
    expect(sourceCode).toMatch(/allDone\s*\?/);
  });
});

// ---------------------------------------------------------------------------
// 21. Batch progress bar (Req 5)
// ---------------------------------------------------------------------------

describe("batch progress bar", () => {
  it("shows progress bar only when batchJobId is set", () => {
    expect(sourceCode).toMatch(/\{batchJobId\s*&&/);
  });

  it("displays current segment being rendered", () => {
    expect(sourceCode).toMatch(/batchProgress\.currentSegment/);
  });

  it("uses dynamic width style for progress bar", () => {
    expect(sourceCode).toMatch(/style=\{\{\s*width\s*:\s*`\$\{batchProgress\.percent\}%`\s*\}\}/);
  });

  it("displays completed count and total", () => {
    expect(sourceCode).toMatch(/batchProgress\.completedCount/);
    expect(sourceCode).toMatch(/batchProgress\.total/);
  });

  it("displays percent value", () => {
    expect(sourceCode).toMatch(/batchProgress\.percent/);
  });

  it("uses emerald-500 color for progress bar fill", () => {
    expect(sourceCode).toMatch(/bg-emerald-500/);
  });
});

// ---------------------------------------------------------------------------
// 22. Segment table structure (Req 3)
// ---------------------------------------------------------------------------

describe("segment table structure", () => {
  it("uses grid-cols-6 for table header", () => {
    expect(sourceCode).toMatch(/grid\s+grid-cols-6/);
  });

  it("includes # column header", () => {
    expect(sourceCode).toMatch(/<div>#<\/div>/);
  });

  it("includes Segment ID column header", () => {
    expect(sourceCode).toMatch(/Segment ID/);
  });

  it("includes Status column header", () => {
    expect(sourceCode).toMatch(/Status/);
  });

  it("includes Play column header", () => {
    expect(sourceCode).toMatch(/Play/);
  });

  it("includes Re-render column header", () => {
    expect(sourceCode).toMatch(/Re-render/);
  });

  it("maps segments to rows", () => {
    expect(sourceCode).toMatch(/segments\.map\s*\(\s*\(seg\s*,\s*idx\)\s*=>/);
  });

  it("displays 1-based row index", () => {
    expect(sourceCode).toMatch(/idx\s*\+\s*1/);
  });

  it("displays segment ID in monospace font", () => {
    expect(sourceCode).toMatch(/font-mono[\s\S]*?seg\.id/);
  });

  it("shows loading message when loading", () => {
    expect(sourceCode).toMatch(/Loading segments\.\.\./);
  });

  it("shows no segments message when empty", () => {
    expect(sourceCode).toMatch(/No segments found\./);
  });
});

// ---------------------------------------------------------------------------
// 23. Play button in table rows (Req 3)
// ---------------------------------------------------------------------------

describe("play button in rows", () => {
  it("renders ▶ play button in each row", () => {
    expect(sourceCode).toMatch(/▶/);
  });

  it("play button stops event propagation", () => {
    expect(sourceCode).toMatch(/e\.stopPropagation\s*\(\s*\)[\s\S]*?handlePlay/);
  });

  it("play button calls handlePlay with segment id", () => {
    expect(sourceCode).toMatch(/handlePlay\s*\(\s*seg\.id\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 24. Re-render button in table rows (Req 6)
// ---------------------------------------------------------------------------

describe("re-render button in rows", () => {
  it("renders ↺ re-render button in each row", () => {
    expect(sourceCode).toMatch(/↺/);
  });

  it("re-render button stops event propagation", () => {
    expect(sourceCode).toMatch(/e\.stopPropagation\s*\(\s*\)[\s\S]*?handleRowRerender/);
  });

  it("re-render button calls handleRowRerender with segment id", () => {
    expect(sourceCode).toMatch(/handleRowRerender\s*\(\s*seg\.id\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 25. Row expansion (Req 4)
// ---------------------------------------------------------------------------

describe("row expansion", () => {
  it("toggles expansion on row click", () => {
    expect(sourceCode).toMatch(/onClick=\{\(\)\s*=>\s*handleRowToggle\s*\(\s*seg\.id\s*\)\s*\}/);
  });

  it("checks if row is expanded via expandedId comparison", () => {
    expect(sourceCode).toMatch(/expandedId\s*===\s*seg\.id/);
  });

  it("shows ▲ indicator when expanded", () => {
    expect(sourceCode).toMatch(/isExpanded\s*\?\s*['"]▲['"]\s*:\s*['"]▼['"]/);
  });

  it("renders waveform container div with ref callback", () => {
    expect(sourceCode).toMatch(/ref=\{\(el\)\s*=>\s*\{\s*waveformRefs\.current\.set\s*\(\s*seg\.id\s*,\s*el\s*\)\s*;\s*\}\s*\}/);
  });

  it("displays segment text below waveform", () => {
    expect(sourceCode).toMatch(/seg\.text/);
  });

  it("uses whitespace-pre-line for text display", () => {
    expect(sourceCode).toMatch(/whitespace-pre-line/);
  });
});

// ---------------------------------------------------------------------------
// 26. Inline SseLogPanel for per-row re-render (Req 6)
// ---------------------------------------------------------------------------

describe("inline SseLogPanel for per-row re-render", () => {
  it("renders SseLogPanel when rowJobIds has a job for the segment", () => {
    expect(sourceCode).toMatch(/rowJobIds\[seg\.id\]/);
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes jobId prop from rowJobIds", () => {
    expect(sourceCode).toMatch(/jobId=\{rowJobIds\[seg\.id\]/);
  });

  it("passes onDone callback that clears the job and re-fetches segments", () => {
    expect(sourceCode).toMatch(/onDone=\{\(\)\s*=>\s*\{/);
    expect(sourceCode).toMatch(/setRowJobIds\s*\(\s*\(prev\)\s*=>\s*\(\s*\{\s*\.\.\.prev\s*,\s*\[seg\.id\]\s*:\s*null\s*\}\s*\)\s*\)/);
  });

  it("passes onError callback that clears the job and re-fetches segments", () => {
    expect(sourceCode).toMatch(/onError=\{\(\)\s*=>\s*\{/);
  });

  it("calls fetchSegments on SseLogPanel done", () => {
    expect(sourceCode).toMatch(/onDone[\s\S]*?fetchSegments\s*\(\s*\)/);
  });

  it("calls fetchSegments on SseLogPanel error", () => {
    expect(sourceCode).toMatch(/onError[\s\S]*?fetchSegments\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 27. Error display
// ---------------------------------------------------------------------------

describe("error display", () => {
  it("conditionally renders error message", () => {
    expect(sourceCode).toMatch(/\{error\s*&&/);
  });

  it("uses red styling for error display", () => {
    expect(sourceCode).toMatch(/bg-red-900\/30\s+border\s+border-red-700\s+text-red-400/);
  });
});

// ---------------------------------------------------------------------------
// 28. Layout and structure
// ---------------------------------------------------------------------------

describe("layout and structure", () => {
  it("uses p-6 space-y-6 for main layout", () => {
    expect(sourceCode).toMatch(/className="p-6\s+space-y-6"/);
  });

  it("uses flex items-center justify-between for toolbar", () => {
    expect(sourceCode).toMatch(/flex\s+items-center\s+justify-between/);
  });

  it("uses flex justify-end for bottom advance button", () => {
    expect(sourceCode).toMatch(/flex\s+justify-end/);
  });

  it("renders two Advance → buttons (top and bottom)", () => {
    const matches = sourceCode.match(/Advance →/g);
    expect(matches).not.toBeNull();
    expect(matches!.length).toBeGreaterThanOrEqual(2);
  });
});
