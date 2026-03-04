/**
 * Tests for components/stages/Stage7VeoGeneration.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage7_veo_generation_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Left column: Character References panel with thumbnail per portrait and [↺ Regenerate] per reference. POST /api/pipeline/veo/references/run.
 *   3. Left column: Frame Chaining display showing text-based chain: clip1 → clip2 → clip3 per section.
 *   4. Right column: Clip list table — columns: clip ID, section, aspect ratio, status badge, stale ⚠ warning, [↺ per-clip regenerate].
 *   5. Toolbar: [Generate All] / [Generate Missing] / section dropdown for [Generate Section].
 *   6. Auto-composite checkbox for paired 9:16 and 16:9 clips composited as split-screen.
 *   7. SSE progress shows per-clip events.
 *   8. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage7VeoGeneration.tsx");
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

  it("exports Stage7VeoGeneration", () => {
    expect(sourceCode).toMatch(/export\s+(default\s+function|const|default)\s+Stage7VeoGeneration/);
  });

  it("has a default export", () => {
    expect(sourceCode).toMatch(/export\s+default/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage7VeoGeneration props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage7VeoGenerationProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage7VeoGenerationProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 4. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React from react", () => {
    expect(sourceCode).toMatch(/import\s+React/);
    expect(sourceCode).toMatch(/from\s+['"]react['"]/);
  });

  it("imports useState from react", () => {
    expect(sourceCode).toMatch(/useState/);
  });

  it("imports useEffect from react", () => {
    expect(sourceCode).toMatch(/useEffect/);
  });

  it("imports useMemo from react", () => {
    expect(sourceCode).toMatch(/useMemo/);
  });

  it("imports SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s+\{?\s*SseLogPanel\s*\}?\s+from/);
  });
});

// ---------------------------------------------------------------------------
// 5. Type definitions
// ---------------------------------------------------------------------------

describe("type definitions", () => {
  it("defines VeoClipStatus type with done, generating, missing, error", () => {
    expect(sourceCode).toMatch(/type\s+VeoClipStatus\s*=/);
    expect(sourceCode).toContain("'done'");
    expect(sourceCode).toContain("'generating'");
    expect(sourceCode).toContain("'missing'");
    expect(sourceCode).toContain("'error'");
  });

  it("defines VeoClip interface with id, sectionId, aspectRatio, status fields", () => {
    expect(sourceCode).toMatch(/interface\s+VeoClip/);
    expect(sourceCode).toMatch(/id\s*:\s*string/);
    expect(sourceCode).toMatch(/sectionId\s*:\s*string/);
    expect(sourceCode).toMatch(/aspectRatio\s*:\s*string/);
    expect(sourceCode).toMatch(/status\s*:\s*VeoClipStatus/);
  });

  it("VeoClip has optional stale boolean field", () => {
    expect(sourceCode).toMatch(/stale\?\s*:\s*boolean/);
  });

  it("VeoClip has optional frameChainDeps string array field", () => {
    expect(sourceCode).toMatch(/frameChainDeps\?\s*:\s*string\[\]/);
  });

  it("defines ReferencePortrait interface with id and optional label", () => {
    expect(sourceCode).toMatch(/interface\s+ReferencePortrait/);
    expect(sourceCode).toMatch(/label\?\s*:\s*string/);
  });

  it("defines ClipLog interface with clipId, message, ts", () => {
    expect(sourceCode).toMatch(/interface\s+ClipLog/);
    expect(sourceCode).toMatch(/clipId\s*:\s*string/);
    expect(sourceCode).toMatch(/message\s*:\s*string/);
    expect(sourceCode).toMatch(/ts\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 6. Status badge function (Req 4 — status badges)
// ---------------------------------------------------------------------------

describe("statusBadge function", () => {
  it("defines statusBadge function", () => {
    expect(sourceCode).toMatch(/const\s+statusBadge\s*=/);
  });

  it("done status renders green ● indicator", () => {
    expect(sourceCode).toMatch(/case\s+['"]done['"]/);
    expect(sourceCode).toMatch(/text-green-500/);
    expect(sourceCode).toContain("● done");
  });

  it("generating status renders amber ◌ indicator with pulse animation", () => {
    expect(sourceCode).toMatch(/case\s+['"]generating['"]/);
    expect(sourceCode).toMatch(/text-amber-500/);
    expect(sourceCode).toMatch(/animate-pulse/);
    expect(sourceCode).toContain("◌ generating");
  });

  it("missing status renders gray ○ indicator", () => {
    expect(sourceCode).toMatch(/case\s+['"]missing['"]/);
    expect(sourceCode).toMatch(/text-slate-400/);
    expect(sourceCode).toContain("○ missing");
  });

  it("error status renders red ✕ indicator", () => {
    expect(sourceCode).toMatch(/case\s+['"]error['"]/);
    expect(sourceCode).toMatch(/text-red-500/);
    expect(sourceCode).toContain("✕ error");
  });
});

// ---------------------------------------------------------------------------
// 7. State management
// ---------------------------------------------------------------------------

describe("state management", () => {
  it("tracks clips state as VeoClip[]", () => {
    expect(sourceCode).toMatch(/\[\s*clips\s*,\s*setClips\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*VeoClip\[\]\s*>/);
  });

  it("tracks references state as ReferencePortrait[]", () => {
    expect(sourceCode).toMatch(/\[\s*references\s*,\s*setReferences\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*ReferencePortrait\[\]\s*>/);
  });

  it("tracks loading state", () => {
    expect(sourceCode).toMatch(/\[\s*loading\s*,\s*setLoading\s*\]/);
  });

  it("tracks error state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*error\s*,\s*setError\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>/);
  });

  it("tracks selectedSection state", () => {
    expect(sourceCode).toMatch(/\[\s*selectedSection\s*,\s*setSelectedSection\s*\]/);
  });

  it("tracks autoComposite state as boolean", () => {
    expect(sourceCode).toMatch(/\[\s*autoComposite\s*,\s*setAutoComposite\s*\]/);
  });

  it("tracks logs state as ClipLog[]", () => {
    expect(sourceCode).toMatch(/\[\s*logs\s*,\s*setLogs\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*ClipLog\[\]\s*>/);
  });

  it("tracks jobId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*jobId\s*,\s*setJobId\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 8. Clip loading on mount
// ---------------------------------------------------------------------------

describe("clip loading on mount", () => {
  it("fetches clips from GET /api/pipeline/veo/clips", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/veo\/clips['"]\s*\)/);
  });

  it("handles loading state correctly", () => {
    expect(sourceCode).toMatch(/setLoading\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setLoading\s*\(\s*false\s*\)/);
  });

  it("handles fetch errors", () => {
    expect(sourceCode).toMatch(/setError/);
  });

  it("sets clips state from fetched data", () => {
    expect(sourceCode).toMatch(/setClips\s*\(/);
  });

  it("sets references state from fetched data", () => {
    expect(sourceCode).toMatch(/setReferences\s*\(/);
  });

  it("initializes selectedSection from first clip", () => {
    expect(sourceCode).toMatch(/setSelectedSection\s*\(\s*fetchedClips\[0\]\.sectionId\s*\)/);
  });

  it("uses useEffect for mount-time fetch", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{/);
  });
});

// ---------------------------------------------------------------------------
// 9. SSE progress for per-clip events (Req 7)
// ---------------------------------------------------------------------------

describe("SSE progress for per-clip events", () => {
  it("creates EventSource for /api/pipeline/veo/stream", () => {
    expect(sourceCode).toMatch(/new\s+EventSource\s*\(\s*['"]\/api\/pipeline\/veo\/stream['"]\s*\)/);
  });

  it("parses incoming SSE message data as JSON", () => {
    expect(sourceCode).toMatch(/JSON\.parse\s*\(\s*event\.data\s*\)/);
  });

  it("appends log entries with clipId and message", () => {
    expect(sourceCode).toMatch(/data\.clipId\s*&&\s*data\.message/);
    expect(sourceCode).toMatch(/setLogs\s*\(\s*\(prev\)\s*=>/);
  });

  it("updates clip status from SSE data", () => {
    expect(sourceCode).toMatch(/data\.clipId\s*&&\s*data\.status/);
  });

  it("closes EventSource on cleanup", () => {
    expect(sourceCode).toMatch(/es\.close\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 10. Computed values (sections and clipsBySection)
// ---------------------------------------------------------------------------

describe("computed values", () => {
  it("computes unique sections from clips using useMemo", () => {
    expect(sourceCode).toMatch(/sections\s*=\s*useMemo/);
    expect(sourceCode).toMatch(/new\s+Set\s*\(\s*clips\.map/);
  });

  it("computes clipsBySection grouping using useMemo", () => {
    expect(sourceCode).toMatch(/clipsBySection\s*=\s*useMemo/);
  });
});

// ---------------------------------------------------------------------------
// 11. Character References panel (Req 2)
// ---------------------------------------------------------------------------

describe("Character References panel", () => {
  it("renders Character References heading", () => {
    expect(sourceCode).toContain("Character References");
  });

  it("renders reference portrait thumbnail with correct src pattern", () => {
    expect(sourceCode).toMatch(/src=\{`\/api\/video\/outputs\/veo\/references\/\$\{ref\.id\}\.png`\}/);
  });

  it("thumbnail has w-16 h-16 object-cover rounded classes", () => {
    expect(sourceCode).toMatch(/className="w-16 h-16 object-cover rounded"/);
  });

  it("renders ↺ Regenerate button per reference", () => {
    expect(sourceCode).toMatch(/↺ Regenerate/);
  });

  it("regenerate reference POSTs to /api/pipeline/veo/references/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/veo\/references\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("sends referenceId in regenerate request body", () => {
    expect(sourceCode).toMatch(/referenceId\s*:\s*refId/);
  });

  it("shows empty state when no references found", () => {
    expect(sourceCode).toMatch(/No reference portraits found/);
  });

  it("maps references to rendered items", () => {
    expect(sourceCode).toMatch(/references\.map\s*\(/);
  });

  it("displays reference label or id", () => {
    expect(sourceCode).toMatch(/ref\.label\s*\?\?\s*ref\.id/);
  });
});

// ---------------------------------------------------------------------------
// 12. Frame Chaining display (Req 3)
// ---------------------------------------------------------------------------

describe("Frame Chaining display", () => {
  it("renders Frame Chaining heading", () => {
    expect(sourceCode).toContain("Frame Chaining");
  });

  it("renders frame chain from frameChainDeps with arrow notation", () => {
    expect(sourceCode).toMatch(/deps\.join\s*\(\s*['"] → ['"]\s*\)/);
    expect(sourceCode).toMatch(/→ \$\{clip\.id\}/);
  });

  it("renders just clipId when no deps exist", () => {
    expect(sourceCode).toMatch(/deps\.length\s*>\s*0\s*\?/);
    expect(sourceCode).toMatch(/:\s*clip\.id/);
  });

  it("groups frame chains by section", () => {
    expect(sourceCode).toMatch(/Object\.entries\s*\(\s*clipsBySection\s*\)/);
  });

  it("renders section id label for each group", () => {
    expect(sourceCode).toMatch(/\{sectionId\}/);
  });
});

// ---------------------------------------------------------------------------
// 13. Clip list table (Req 4)
// ---------------------------------------------------------------------------

describe("clip list table", () => {
  it("renders table element", () => {
    expect(sourceCode).toMatch(/<table/);
  });

  it("renders Clip column header", () => {
    expect(sourceCode).toMatch(/>Clip</);
  });

  it("renders Section column header", () => {
    expect(sourceCode).toMatch(/>Section</);
  });

  it("renders Aspect column header", () => {
    expect(sourceCode).toMatch(/>Aspect</);
  });

  it("renders Status column header", () => {
    expect(sourceCode).toMatch(/>Status</);
  });

  it("renders Actions column header", () => {
    expect(sourceCode).toMatch(/>Actions</);
  });

  it("maps clips to table rows", () => {
    expect(sourceCode).toMatch(/clips\.map\s*\(\s*\(clip\)\s*=>/);
  });

  it("displays clip.id in table row", () => {
    expect(sourceCode).toMatch(/\{clip\.id\}/);
  });

  it("displays clip.sectionId in table row", () => {
    expect(sourceCode).toMatch(/\{clip\.sectionId\}/);
  });

  it("displays clip.aspectRatio in table row", () => {
    expect(sourceCode).toMatch(/\{clip\.aspectRatio\}/);
  });

  it("renders statusBadge for each clip", () => {
    expect(sourceCode).toMatch(/statusBadge\s*\(\s*clip\.status\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Stale indicator (Req 4 — stale ⚠ warning)
// ---------------------------------------------------------------------------

describe("stale indicator", () => {
  it("shows ⚠ warning when clip.stale is true", () => {
    expect(sourceCode).toMatch(/clip\.stale/);
    expect(sourceCode).toContain("⚠");
  });

  it("stale indicator has amber color", () => {
    expect(sourceCode).toMatch(/text-amber-500/);
  });
});

// ---------------------------------------------------------------------------
// 15. Per-clip regenerate (Req 4)
// ---------------------------------------------------------------------------

describe("per-clip regenerate", () => {
  it("renders ↺ Regenerate button per clip in table", () => {
    // Multiple Regenerate buttons exist — one per reference, one per clip
    const matches = sourceCode.match(/↺ Regenerate/g);
    expect(matches).not.toBeNull();
    expect(matches!.length).toBeGreaterThanOrEqual(2);
  });

  it("per-clip regenerate POSTs to /api/pipeline/veo/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/veo\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("sends clips array in run request body", () => {
    expect(sourceCode).toMatch(/body\s*:\s*JSON\.stringify\s*\(\s*\{\s*clips\s*:/);
  });

  it("handleRunClips sets clip status to generating optimistically", () => {
    expect(sourceCode).toMatch(/status\s*:\s*['"]generating['"]/);
  });
});

// ---------------------------------------------------------------------------
// 16. Toolbar (Req 5)
// ---------------------------------------------------------------------------

describe("toolbar", () => {
  it("renders Generate All button", () => {
    expect(sourceCode).toContain("Generate All");
  });

  it("Generate All triggers handleRunClips with all clip ids", () => {
    expect(sourceCode).toMatch(/handleRunClips\s*\(\s*clips\.map\s*\(\s*\(c\)\s*=>\s*c\.id\s*\)\s*\)/);
  });

  it("renders Generate Missing button", () => {
    expect(sourceCode).toContain("Generate Missing");
  });

  it("Generate Missing filters for clips with status missing", () => {
    expect(sourceCode).toMatch(/clips\.filter\s*\(\s*\(c\)\s*=>\s*c\.status\s*===\s*['"]missing['"]\s*\)/);
  });

  it("renders section dropdown select", () => {
    expect(sourceCode).toMatch(/<select/);
    expect(sourceCode).toMatch(/selectedSection/);
  });

  it("section dropdown populated from sections array", () => {
    expect(sourceCode).toMatch(/sections\.map\s*\(/);
    expect(sourceCode).toMatch(/<option/);
  });

  it("renders Generate Section button", () => {
    expect(sourceCode).toContain("Generate Section");
  });

  it("Generate Section filters clips by selectedSection", () => {
    expect(sourceCode).toMatch(/clips\.filter\s*\(\s*\(c\)\s*=>\s*c\.sectionId\s*===\s*selectedSection\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 17. Auto-composite checkbox (Req 6)
// ---------------------------------------------------------------------------

describe("auto-composite checkbox", () => {
  it("renders auto-composite checkbox input", () => {
    expect(sourceCode).toMatch(/<input[\s\S]*?type="checkbox"/);
    expect(sourceCode).toMatch(/checked=\{autoComposite\}/);
  });

  it("renders Auto-composite split-screen label", () => {
    expect(sourceCode).toContain("Auto-composite split-screen");
  });

  it("sends autoComposite flag in run request body", () => {
    expect(sourceCode).toMatch(/autoComposite/);
    expect(sourceCode).toMatch(/JSON\.stringify\s*\(\s*\{\s*clips\s*:\s*clipIds\s*,\s*autoComposite\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 18. SSE Log Panel
// ---------------------------------------------------------------------------

describe("SSE log panel", () => {
  it("renders SseLogPanel component", () => {
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes jobId to SseLogPanel", () => {
    expect(sourceCode).toMatch(/jobId=\{jobId\}/);
  });
});

// ---------------------------------------------------------------------------
// 19. Per-clip log events
// ---------------------------------------------------------------------------

describe("per-clip log events", () => {
  it("renders Clip Events heading", () => {
    expect(sourceCode).toContain("Clip Events");
  });

  it("maps logs to rendered entries", () => {
    expect(sourceCode).toMatch(/logs\.map\s*\(/);
  });

  it("displays clipId and message in each log entry", () => {
    expect(sourceCode).toMatch(/log\.clipId/);
    expect(sourceCode).toMatch(/log\.message/);
  });

  it("log container has max-height with overflow scroll", () => {
    expect(sourceCode).toMatch(/max-h-40/);
    expect(sourceCode).toMatch(/overflow-y-auto/);
  });

  it("log uses monospace font", () => {
    expect(sourceCode).toMatch(/font-mono/);
  });
});

// ---------------------------------------------------------------------------
// 20. Loading and error states
// ---------------------------------------------------------------------------

describe("loading and error states", () => {
  it("shows loading message while fetching clips", () => {
    expect(sourceCode).toMatch(/Loading Veo clips/);
  });

  it("shows error message when fetch fails", () => {
    expect(sourceCode).toMatch(/Error:/);
  });
});

// ---------------------------------------------------------------------------
// 21. Continue / Advance button
// ---------------------------------------------------------------------------

describe("Continue / Advance button", () => {
  it("renders Continue button", () => {
    expect(sourceCode).toContain("Continue");
  });

  it("Continue button calls onAdvance on click", () => {
    expect(sourceCode).toMatch(/onClick=\{onAdvance\}/);
  });
});

// ---------------------------------------------------------------------------
// 22. Layout structure
// ---------------------------------------------------------------------------

describe("layout structure", () => {
  it("uses two-column layout with left 1/3 and flex-1 right", () => {
    expect(sourceCode).toMatch(/w-1\/3/);
    expect(sourceCode).toMatch(/flex-1/);
  });

  it("uses flex gap for main layout", () => {
    expect(sourceCode).toMatch(/flex\s+gap-6/);
  });

  it("uses dark-themed rounded-lg shadow for card panels", () => {
    expect(sourceCode).toMatch(/bg-slate-900 rounded-lg shadow/);
  });
});

// ---------------------------------------------------------------------------
// 23. API endpoints verification
// ---------------------------------------------------------------------------

describe("API endpoints", () => {
  it("uses GET /api/pipeline/veo/clips for loading clips", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/veo\/clips['"]/);
  });

  it("uses POST /api/pipeline/veo/run for running clips", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/veo\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("uses POST /api/pipeline/veo/references/run for regenerating references", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/veo\/references\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("uses /api/pipeline/veo/stream for SSE events", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/veo\/stream['"]/);
  });

  it("uses /api/video/outputs/veo/references/ for reference thumbnails", () => {
    expect(sourceCode).toMatch(/\/api\/video\/outputs\/veo\/references\//);
  });
});

// ---------------------------------------------------------------------------
// Dark theme compliance
// ---------------------------------------------------------------------------

describe("Dark theme compliance", () => {
  it("panels use dark background instead of bg-white", () => {
    expect(sourceCode).not.toMatch(/className="[^"]*bg-white rounded[^"]*"/);
    expect(sourceCode).not.toMatch(/className="[^"]*bg-white rounded-lg[^"]*"/);
  });

  it("heading text uses light color for dark theme", () => {
    expect(sourceCode).not.toMatch(/text-slate-800/);
  });

  it("body text uses dark-theme-friendly colors", () => {
    expect(sourceCode).not.toMatch(/className="[^"]*text-slate-700[^"]*"/);
  });

  it("table header uses dark background", () => {
    expect(sourceCode).not.toMatch(/bg-slate-100 text-slate-600/);
  });

  it("section select uses dark theme styling", () => {
    expect(sourceCode).not.toMatch(/text-slate-800 bg-white/);
  });

  it("panels use dark background class", () => {
    expect(sourceCode).toMatch(/bg-slate-900/);
  });
});

// ---------------------------------------------------------------------------
// Regenerate reference error handling and progress (bug fix)
// ---------------------------------------------------------------------------

describe("Regenerate reference error handling and progress", () => {
  it("checks response status after regenerate reference request", () => {
    expect(sourceCode).toMatch(/!res\.ok/);
  });

  it("extracts jobId from SSE response for reference regeneration", () => {
    expect(sourceCode).toMatch(/extractJobIdFromSse/);
  });

  it("tracks regenerating reference ID for loading state", () => {
    expect(sourceCode).toMatch(/regeneratingRefId/);
  });

  it("passes onDone to SseLogPanel to refresh after regeneration", () => {
    expect(sourceCode).toMatch(/onDone=\{fetchClips\}/);
  });
});
