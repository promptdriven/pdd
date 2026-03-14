/**
 * Tests for components/stages/Stage8CompositionGen.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage8_composition_gen_TypeScriptReact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Left: component list by section (collapsible). Each component row: name, status badge, [Preview] button, [↺] per-component regenerate.
 *   3. Section wrappers listed separately below components.
 *   4. [Generate All Compositions] runs POST /api/pipeline/compositions/run.
 *   5. Right: asset staging manifest table — columns: filename, expected (✓/✗), present (✓/✗), [Stage Now] button for missing files.
 *   6. [Stage All Missing] button runs POST /api/pipeline/asset-staging/run without opening a fake job log.
 *   7. Error status shows last error message in a tooltip on hover.
 *   8. Log drawer (expandable) shows SSE log for the active job.
 *   9. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage8CompositionGen.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive (Req 9)
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

  it("exports Stage8CompositionGen", () => {
    expect(sourceCode).toMatch(/export\s+(default\s+function|const|default)\s+Stage8CompositionGen/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage8CompositionGen props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage8CompositionGenProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage8CompositionGenProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 4. API Endpoints
// ---------------------------------------------------------------------------

describe("API endpoints", () => {
  it("uses GET /api/pipeline/compositions/list", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/compositions\/list['"]/);
  });

  it("reads artifactState from the composition list response", () => {
    expect(sourceCode).toMatch(/artifactState/);
  });

  it("uses GET /api/pipeline/veo/staging-manifest", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/veo\/staging-manifest['"]/);
  });

  it("uses GET /api/pipeline/compositions/preview", () => {
    expect(sourceCode).toMatch(/[`'"]\/api\/pipeline\/compositions\/preview\?component=/);
  });

  it("uses POST /api/pipeline/compositions/run", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/compositions\/run['"]/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("uses POST /api/pipeline/asset-staging/run", () => {
    expect(sourceCode).toMatch(/['"]\/api\/pipeline\/asset-staging\/run['"]/);
  });
});

// ---------------------------------------------------------------------------
// 5. Left Panel: Component List (Req 2)
// ---------------------------------------------------------------------------

describe("Left Panel: Component List", () => {
  it("renders status badge", () => {
    expect(sourceCode).toMatch(/StatusBadge/);
  });

  it("renders Preview button", () => {
    expect(sourceCode).toContain("Preview");
  });

  it("opens modal for preview", () => {
    expect(sourceCode).toMatch(/<dialog/);
    expect(sourceCode).toMatch(/showModal/);
  });

  it("preview fetches PNG still", () => {
    // Implicitly checked by API endpoint test, but checking usage
    expect(sourceCode).toMatch(/setPreviewUrl/);
  });

  it("tracks associated spec metadata for the preview modal", () => {
    expect(sourceCode).toMatch(/setPreviewSpecContent/);
    expect(sourceCode).toMatch(/setPreviewSpecPath/);
  });

  it("tracks stale preview errors for the preview modal", () => {
    expect(sourceCode).toMatch(/setPreviewError/);
  });

  it("renders an Associated Spec pane beside the preview", () => {
    expect(sourceCode).toContain("Associated Spec");
    expect(sourceCode).toMatch(/previewSpecContent/);
    expect(sourceCode).toMatch(/previewSpecPath/);
  });

  it("renders Regenerate button (symbol or text)", () => {
    expect(sourceCode).toMatch(/↺/); // The code uses the symbol
  });

  it("regenerate triggers POST /api/pipeline/compositions/run with component name", () => {
    // Check for correct payload structure
    expect(sourceCode).toMatch(/components\s*:\s*\[/);
  });
});

// ---------------------------------------------------------------------------
// 6. Section Wrappers (Req 3)
// ---------------------------------------------------------------------------

describe("Section Wrappers", () => {
  it("renders Section Wrappers heading or section", () => {
    expect(sourceCode).toContain("Section Wrappers");
  });

  it("lists wrappers separately", () => {
    // Check that it iterates over wrappers
    expect(sourceCode).toMatch(/sectionWrappers\.map/);
  });
});

// ---------------------------------------------------------------------------
// 7. Generate All (Req 4)
// ---------------------------------------------------------------------------

describe("Generate All Button", () => {
  it("renders Generate All Compositions button", () => {
    expect(sourceCode).toContain("Generate All Compositions");
  });

  it("renders a stale artifact warning when generated outputs are out of date", () => {
    expect(sourceCode).toContain("Generated composition outputs are stale");
    expect(sourceCode).toContain("Regenerate compositions");
  });

  it("triggers runJob with correct endpoint", () => {
    expect(sourceCode).toMatch(/runJob\(\s*['"]\/api\/pipeline\/compositions\/run['"]\s*,/);
  });
});

// ---------------------------------------------------------------------------
// 8. Right Panel: Staging Manifest (Req 5 & 6)
// ---------------------------------------------------------------------------

describe("Right Panel: Staging Manifest", () => {
  it("renders Asset Staging Manifest heading", () => {
    expect(sourceCode).toContain("Asset Staging Manifest");
  });

  it("renders table with Filename, Expected, Present columns", () => {
    expect(sourceCode).toContain("Filename");
    expect(sourceCode).toContain("Expected");
    expect(sourceCode).toContain("Present");
  });

  it("renders Stage Now button", () => {
    expect(sourceCode).toContain("Stage Now");
  });

  it("renders Stage All Missing button", () => {
    expect(sourceCode).toContain("Stage All Missing");
  });

  it("Stage All Missing triggers dedicated asset staging handler", () => {
     expect(sourceCode).toMatch(/runAssetStaging\s*\(/);
     expect(sourceCode).not.toMatch(/runJob\(\s*['"]\/api\/pipeline\/asset-staging\/run['"]\s*,/);
  });

  it("Stage Now buttons use the dedicated asset staging handler", () => {
    expect(sourceCode).toMatch(/runAssetStaging\s*\(\s*\[entry\.filename\]/);
  });
});

// ---------------------------------------------------------------------------
// 9. Error Tooltip (Req 7)
// ---------------------------------------------------------------------------

describe("Error Tooltip", () => {
  it("renders title attribute on status badge for error", () => {
    expect(sourceCode).toMatch(/title=\{status === ['"]error['"] && error \? error : undefined\}/);
  });
});

// ---------------------------------------------------------------------------
// 10. Log Drawer (Req 8)
// ---------------------------------------------------------------------------

describe("Log Drawer", () => {
  it("renders Job Logs toggle", () => {
    expect(sourceCode).toContain("Job Logs");
  });

  it("renders SseLogPanel", () => {
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes jobId to SseLogPanel", () => {
    expect(sourceCode).toMatch(/jobId=\{activeJobId\}/);
  });

  it("clears the active job id when SseLogPanel completes", () => {
    expect(sourceCode).toMatch(/onDone=\{\(\)\s*=>\s*\{[\s\S]*setActiveJobId\(null\);[\s\S]*refreshData\(\);[\s\S]*\}\}/);
  });

  it("clears the active job id when SseLogPanel errors", () => {
    expect(sourceCode).toMatch(/onError=\{\(\)\s*=>\s*\{[\s\S]*setActiveJobId\(null\);[\s\S]*refreshData\(\);[\s\S]*\}\}/);
  });
});

// ---------------------------------------------------------------------------
// 11. Dark theme compliance
// ---------------------------------------------------------------------------

describe("Dark theme compliance", () => {
  it("panels use dark background instead of bg-white", () => {
    expect(sourceCode).not.toMatch(/border-slate-200 bg-white/);
  });

  it("text elements use light colors for dark theme", () => {
    // Should not have text-slate-700 which is too dark
    const nonStringMatches = sourceCode.match(/className="[^"]*text-slate-700[^"]*"/g) || [];
    expect(nonStringMatches.length).toBe(0);
  });

  it("StatusBadge pending uses dark theme colors", () => {
    expect(sourceCode).not.toMatch(/bg-slate-100 text-slate-600/);
    expect(sourceCode).toMatch(/bg-slate-700 text-slate-200 border-slate-600/);
  });

  it("dividers use dark slate borders", () => {
    expect(sourceCode).not.toMatch(/divide-slate-100/);
    expect(sourceCode).not.toMatch(/border-slate-100/);
  });

  it("error messages use dark theme (not bg-red-50)", () => {
    expect(sourceCode).not.toMatch(/bg-red-50/);
    expect(sourceCode).toMatch(/bg-red-900/);
  });
});
