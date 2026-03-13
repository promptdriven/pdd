/**
 * Tests for components/stages/Stage9RenderStitch.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage9_render_stitch_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Section render table: columns section ID, duration (seconds), status badge,
 *      progress bar (0–100%), [▶] modal preview, [↺] re-render.
 *   3. Active renders panel: shows up to 3 simultaneous progress bars (each labeled with section ID).
 *   4. [Render ▾] dropdown: options All / Missing / Selected.
 *      Triggers POST /api/pipeline/render/run with appropriate { sections }.
 *   5. [Stitch Full Video] button: triggers POST /api/pipeline/stitch/run.
 *      Disabled while renders are in progress.
 *   6. Full Video panel: shows file size, duration, [Continue →] button that calls onAdvance().
 *   7. All progress bars update via SSE stream for the active render job.
 *   8. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage9RenderStitch.tsx");
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

  it("exports Stage9RenderStitch", () => {
    expect(sourceCode).toMatch(/export\s+(default\s+function|const|default)\s+Stage9RenderStitch/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage9RenderStitch props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage9RenderStitchProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage9RenderStitchProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 4. API Endpoints
// ---------------------------------------------------------------------------

describe("API endpoints", () => {
  it("uses GET /api/pipeline/render/status on mount", () => {
    expect(sourceCode).toMatch(/['"`]\/api\/pipeline\/render\/status['"`]/);
  });

  it("uses POST /api/pipeline/render/run for rendering", () => {
    expect(sourceCode).toMatch(/['"`]\/api\/pipeline\/render\/run['"`]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("uses POST /api/pipeline/stitch/run for stitching", () => {
    expect(sourceCode).toMatch(/['"`]\/api\/pipeline\/stitch\/run['"`]/);
  });

  it("uses SSE stream endpoint for render progress", () => {
    expect(sourceCode).toMatch(/\/api\/pipeline\/render\/stream/);
  });
});

// ---------------------------------------------------------------------------
// 5. Section Render Table (Req 2)
// ---------------------------------------------------------------------------

describe("Section render table", () => {
  it("renders a table element", () => {
    expect(sourceCode).toMatch(/<table/);
  });

  it("has Section ID column", () => {
    expect(sourceCode).toContain("Section ID");
  });

  it("has Duration column", () => {
    expect(sourceCode).toMatch(/Duration/);
  });

  it("has Status column", () => {
    expect(sourceCode).toContain("Status");
  });

  it("has Progress column", () => {
    expect(sourceCode).toContain("Progress");
  });

  it("has Preview column", () => {
    expect(sourceCode).toContain("Preview");
  });

  it("has Re-render column", () => {
    expect(sourceCode).toContain("Re-render");
  });

  it("renders status badges with correct status labels", () => {
    expect(sourceCode).toContain("Rendered");
    expect(sourceCode).toContain("Rendering");
    expect(sourceCode).toContain("Error");
    expect(sourceCode).toContain("Missing");
  });

  it("renders progress bar with spec-required className", () => {
    expect(sourceCode).toMatch(/h-2\s+bg-green-400\s+transition-all/);
  });

  it("renders progress bar with percentage width style", () => {
    expect(sourceCode).toMatch(/width:\s*`\$\{.*progress.*\}%`/);
  });

  it("renders preview button with ▶ symbol", () => {
    expect(sourceCode).toContain("▶");
  });

  it("renders re-render button with ↺ symbol", () => {
    expect(sourceCode).toContain("↺");
  });

  it("displays section duration with toFixed", () => {
    expect(sourceCode).toMatch(/durationSeconds\.toFixed/);
  });

  it("displays progress percentage text", () => {
    expect(sourceCode).toMatch(/\{s\.progress\}%/);
  });
});

// ---------------------------------------------------------------------------
// 6. Section Selection / Checkbox Column (Spec: Section selection for [Selected] mode)
// ---------------------------------------------------------------------------

describe("Section selection", () => {
  it("renders checkbox input for each section", () => {
    expect(sourceCode).toMatch(/<input[\s\S]*?type="checkbox"/);
  });

  it("has Select column header", () => {
    expect(sourceCode).toContain("Select");
  });

  it("manages selected state", () => {
    expect(sourceCode).toMatch(/useState<Record<string,\s*boolean>>/);
  });
});

// ---------------------------------------------------------------------------
// 7. Active Renders Panel (Req 3)
// ---------------------------------------------------------------------------

describe("Active renders panel", () => {
  it("renders Active Renders heading", () => {
    expect(sourceCode).toContain("Active Renders");
  });

  it("filters sections where progress > 0 && progress < 100", () => {
    expect(sourceCode).toMatch(/s\.progress\s*>\s*0\s*&&\s*s\.progress\s*<\s*100/);
  });

  it("limits to 3 simultaneous progress bars", () => {
    expect(sourceCode).toMatch(/\.slice\(0,\s*3\)/);
  });

  it("labels each progress bar with section ID", () => {
    expect(sourceCode).toMatch(/Section:.*\{s\.id\}/s);
  });

  it("renders progress bars in active renders panel", () => {
    // Progress bars within the active renders section
    expect(sourceCode).toMatch(/activeRenders\.map/);
  });
});

// ---------------------------------------------------------------------------
// 8. Render Dropdown (Req 4)
// ---------------------------------------------------------------------------

describe("Render dropdown", () => {
  it("renders a select element with render mode options", () => {
    expect(sourceCode).toMatch(/<select/);
  });

  it("has All option", () => {
    expect(sourceCode).toMatch(/<option\s+value="all">All<\/option>/);
  });

  it("has Missing option", () => {
    expect(sourceCode).toMatch(/<option\s+value="missing">Missing<\/option>/);
  });

  it("has Selected option", () => {
    expect(sourceCode).toMatch(/<option\s+value="selected">Selected<\/option>/);
  });

  it("renders Render ▾ button", () => {
    expect(sourceCode).toContain("Render ▾");
  });

  it("handleRender sends POST /api/pipeline/render/run with sections payload", () => {
    expect(sourceCode).toMatch(/body:\s*JSON\.stringify\(\s*\{\s*sections:\s*toRender\s*\}\s*\)/);
  });

  it("'all' mode sends all section IDs", () => {
    expect(sourceCode).toMatch(/sections\.map\(\s*\(s\)\s*=>\s*s\.id\s*\)/);
  });

  it("'missing' mode filters sections with missing status or zero progress", () => {
    expect(sourceCode).toMatch(/s\.status\s*===\s*['"]missing['"]/);
  });

  it("'selected' mode uses selected state", () => {
    expect(sourceCode).toMatch(/Object\.keys\(selected\)\.filter/);
  });
});

// ---------------------------------------------------------------------------
// 9. Stitch Full Video Button (Req 5)
// ---------------------------------------------------------------------------

describe("Stitch Full Video button", () => {
  it("renders Stitch Full Video button", () => {
    expect(sourceCode).toContain("Stitch Full Video");
  });

  it("triggers POST /api/pipeline/stitch/run", () => {
    expect(sourceCode).toMatch(/fetch\(\s*['"]\/api\/pipeline\/stitch\/run['"]\s*,\s*\{\s*method:\s*['"]POST['"]/);
  });

  it("is disabled while renders are in progress", () => {
    expect(sourceCode).toMatch(/disabled=\{anyRenderInProgress/);
  });

  it("anyRenderInProgress checks for active sections", () => {
    expect(sourceCode).toMatch(/sections\.some\(\s*\(s\)\s*=>\s*s\.progress\s*>\s*0\s*&&\s*s\.progress\s*<\s*100\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 10. Full Video Panel (Req 6)
// ---------------------------------------------------------------------------

describe("Full Video panel", () => {
  it("renders Full Video heading", () => {
    expect(sourceCode).toContain("Full Video");
  });

  it("is visible only when fullVideo.exists is true", () => {
    expect(sourceCode).toMatch(/fullVideo\.exists\s*&&/);
  });

  it("shows file size", () => {
    expect(sourceCode).toMatch(/formatBytes\(fullVideo\.sizeBytes\)/);
  });

  it("shows duration", () => {
    expect(sourceCode).toMatch(/fullVideo\.durationSeconds/);
  });

  it("renders Continue → button", () => {
    expect(sourceCode).toContain("Continue →");
  });

  it("Continue → calls onAdvance()", () => {
    expect(sourceCode).toMatch(/onClick=\{onAdvance\}/);
  });

  it("formatBytes formats as MB", () => {
    expect(sourceCode).toMatch(/MB/);
  });

  it("formatBytes formats as GB", () => {
    expect(sourceCode).toMatch(/GB/);
  });
});

// ---------------------------------------------------------------------------
// 11. SSE Stream Progress (Req 7)
// ---------------------------------------------------------------------------

describe("SSE stream progress", () => {
  it("creates EventSource for render progress", () => {
    expect(sourceCode).toMatch(/new\s+EventSource/);
  });

  it("listens for section-progress events", () => {
    expect(sourceCode).toMatch(/['"]section-progress['"]/);
  });

  it("extracts sectionId and percent from SSE events", () => {
    expect(sourceCode).toMatch(/sectionId/);
    expect(sourceCode).toMatch(/percent/);
  });

  it("clamps progress to 0-100 range", () => {
    expect(sourceCode).toMatch(/Math\.max\(0,\s*Math\.min\(100/);
  });

  it("updates section status to 'done' at 100%", () => {
    expect(sourceCode).toMatch(/percent\s*>=\s*100\s*\?\s*['"]done['"]/);
  });

  it("updates section status to 'rendering' below 100%", () => {
    expect(sourceCode).toMatch(/:\s*['"]rendering['"]/);
  });

  it("closes EventSource on cleanup", () => {
    expect(sourceCode).toMatch(/es\.close\(\)/);
  });

  it("handles render-complete event", () => {
    expect(sourceCode).toMatch(/['"]render-complete['"]/);
  });

  it("handles render-error event", () => {
    expect(sourceCode).toMatch(/['"]render-error['"]/);
  });
});

// ---------------------------------------------------------------------------
// 12. Preview Modal (Spec: Preview modal)
// ---------------------------------------------------------------------------

describe("Preview modal", () => {
  it("renders a video element for preview", () => {
    expect(sourceCode).toMatch(/<video/);
  });

  it("video src follows spec pattern /api/video/outputs/sections/{sectionId}.mp4", () => {
    expect(sourceCode).toMatch(/\/api\/video\/outputs\/sections\/\$\{.*\}\.mp4/);
  });

  it("video has controls attribute", () => {
    expect(sourceCode).toMatch(/<video[\s\S]*?controls/);
  });

  it("video has max-w-full className", () => {
    expect(sourceCode).toMatch(/max-w-full/);
  });

  it("modal has overlay backdrop", () => {
    expect(sourceCode).toMatch(/bg-black\/50/);
  });

  it("modal can be closed by clicking overlay", () => {
    expect(sourceCode).toMatch(/onClick=\{.*\(\)\s*=>\s*setPreviewSectionId\(null\)/);
  });

  it("modal has close button", () => {
    expect(sourceCode).toContain("✕");
  });

  it("modal stops propagation on inner click", () => {
    expect(sourceCode).toMatch(/e\.stopPropagation\(\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Load Status on Mount
// ---------------------------------------------------------------------------

describe("Load status on mount", () => {
  it("fetches render status on mount via useEffect", () => {
    expect(sourceCode).toMatch(/useEffect\(\s*\(\)\s*=>\s*\{[\s\S]*?loadStatus/);
  });

  it("loadStatus fetches GET /api/pipeline/render/status", () => {
    expect(sourceCode).toMatch(/fetch\(\s*['"]\/api\/pipeline\/render\/status['"]\s*\)/);
  });

  it("sets sections from response data", () => {
    expect(sourceCode).toMatch(/setSections\(data\.sections/);
  });

  it("sets fullVideo from response data", () => {
    expect(sourceCode).toMatch(/setFullVideo\(data\.fullVideo/);
  });
});

// ---------------------------------------------------------------------------
// 14. Error Handling
// ---------------------------------------------------------------------------

describe("Error handling", () => {
  it("displays error message when present", () => {
    expect(sourceCode).toMatch(/\{error\s*&&/);
  });

  it("shows error when no sections selected", () => {
    expect(sourceCode).toContain("No sections selected for render.");
  });

  it("handles fetch failure for render status", () => {
    expect(sourceCode).toContain("Failed to load render status.");
  });

  it("handles fetch failure for render job", () => {
    expect(sourceCode).toContain("Failed to start render job.");
  });

  it("handles fetch failure for stitch", () => {
    expect(sourceCode).toContain("Failed to stitch full video.");
  });
});

// ---------------------------------------------------------------------------
// 15. Empty State
// ---------------------------------------------------------------------------

describe("Empty state", () => {
  it("displays message when no sections found", () => {
    expect(sourceCode).toContain("No sections found.");
  });

  it("empty row spans all 7 columns", () => {
    expect(sourceCode).toMatch(/colSpan=\{7\}/);
  });
});

// ---------------------------------------------------------------------------
// 16. React State Management
// ---------------------------------------------------------------------------

describe("React state management", () => {
  it("uses useState for sections", () => {
    expect(sourceCode).toMatch(/useState<SectionRenderStatus\[\]>/);
  });

  it("uses useState for fullVideo", () => {
    expect(sourceCode).toMatch(/useState<FullVideoInfo>/);
  });

  it("uses useState for renderJobId", () => {
    expect(sourceCode).toMatch(/useState<string\s*\|\s*null>/);
  });

  it("uses useMemo for activeRenders", () => {
    expect(sourceCode).toMatch(/useMemo\(\s*\n?\s*\(\)\s*=>\s*sections\.filter/);
  });

  it("uses useMemo for anyRenderInProgress", () => {
    expect(sourceCode).toMatch(/useMemo\(\s*\n?\s*\(\)\s*=>\s*sections\.some/);
  });

  it("uses useRef for EventSource", () => {
    expect(sourceCode).toMatch(/useRef<EventSource\s*\|\s*null>/);
  });

  it("uses useCallback for loadStatus", () => {
    expect(sourceCode).toMatch(/useCallback\(async/);
  });
});

// ---------------------------------------------------------------------------
// 17. Render Mode Type
// ---------------------------------------------------------------------------

describe("Render mode type", () => {
  it("defines RenderMode type with all | missing | selected", () => {
    expect(sourceCode).toMatch(/type\s+RenderMode\s*=\s*['"]all['"]\s*\|\s*['"]missing['"]\s*\|\s*['"]selected['"]/);
  });
});

// ---------------------------------------------------------------------------
// 18. Section Status Types
// ---------------------------------------------------------------------------

describe("Section status types", () => {
  it("defines SectionRenderStatus interface", () => {
    expect(sourceCode).toMatch(/interface\s+SectionRenderStatus/);
  });

  it("SectionRenderStatus includes id field", () => {
    expect(sourceCode).toMatch(/id:\s*string/);
  });

  it("SectionRenderStatus includes durationSeconds field", () => {
    expect(sourceCode).toMatch(/durationSeconds:\s*number/);
  });

  it("SectionRenderStatus includes status field with correct union", () => {
    expect(sourceCode).toMatch(/status:\s*['"]missing['"]\s*\|\s*['"]rendering['"]\s*\|\s*['"]done['"]\s*\|\s*['"]error['"]/);
  });

  it("SectionRenderStatus includes progress field", () => {
    expect(sourceCode).toMatch(/progress:\s*number/);
  });
});

// ---------------------------------------------------------------------------
// 19. FullVideoInfo Interface
// ---------------------------------------------------------------------------

describe("FullVideoInfo interface", () => {
  it("defines FullVideoInfo interface", () => {
    expect(sourceCode).toMatch(/interface\s+FullVideoInfo/);
  });

  it("includes exists boolean field", () => {
    expect(sourceCode).toMatch(/exists:\s*boolean/);
  });

  it("includes optional sizeBytes field", () => {
    expect(sourceCode).toMatch(/sizeBytes\?:\s*number/);
  });

  it("includes optional durationSeconds field", () => {
    expect(sourceCode).toMatch(/durationSeconds\?:\s*number/);
  });
});

// ---------------------------------------------------------------------------
// 20. Dark theme compliance
// ---------------------------------------------------------------------------

describe("Dark theme compliance", () => {
  it("panels use dark background instead of bg-white", () => {
    expect(sourceCode).not.toMatch(/className="[^"]*bg-white[^"]*"/);
  });

  it("select dropdown uses dark theme", () => {
    expect(sourceCode).toMatch(/bg-slate-800/);
  });

  it("disabled stitch button uses dark colors", () => {
    expect(sourceCode).not.toMatch(/bg-slate-300 text-slate-600/);
    expect(sourceCode).toMatch(/bg-slate-700 text-slate-400/);
  });

  it("status badges use dark theme colors", () => {
    expect(sourceCode).not.toMatch(/bg-green-100 text-green-700/);
    expect(sourceCode).toMatch(/bg-green-900/);
  });

  it("error messages use dark theme (not bg-red-50)", () => {
    expect(sourceCode).not.toMatch(/bg-red-50/);
    expect(sourceCode).toMatch(/bg-red-900/);
  });
});

// ---------------------------------------------------------------------------
// 21. handleRerenderSection logic
// ---------------------------------------------------------------------------

describe("handleRerenderSection logic", () => {
  it("renders the specific section by ID instead of relying on selected state", () => {
    // Should pass sectionId directly to fetch, not go through handleRender('selected')
    const funcBody = sourceCode.slice(
      sourceCode.indexOf('handleRerenderSection'),
      sourceCode.indexOf('handleRerenderSection') + 500
    );
    expect(funcBody).toMatch(/sections:\s*\[sectionId\]/);
    expect(funcBody).not.toMatch(/handleRender\('selected'\)/);
  });
});
