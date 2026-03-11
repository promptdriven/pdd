/**
 * Tests for components/StageSidebar.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage_sidebar_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: activeStage: PipelineStage, onStageSelect: (stage: PipelineStage) => void
 *   2. Renders 10 clickable stage rows with: stage number (1–10), stage label, status badge
 *   3. Status badge icons: ○ = not_started, ◌ = running (with pulse), ● = done, ✕ = error
 *   4. Active stage highlighted with distinct left border or background
 *   5. Polls GET /api/pipeline/status every 5 seconds, updates badges, no flicker
 *   6. Error stages show tooltip with error message on hover
 *   7. 'use client' directive
 *   8. Stage labels: Setup, Script, TTS Script, TTS Render, Audio Sync, Spec Gen, Veo Gen, Compositions, Render, Audit
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "StageSidebar.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive
// ---------------------------------------------------------------------------

describe("'use client' directive", () => {
  it("has 'use client' as the very first line", () => {
    const firstLine = sourceCode.split("\n")[0].trim();
    expect(firstLine).toBe("'use client';");
  });
});

// ---------------------------------------------------------------------------
// 2. Props interface
// ---------------------------------------------------------------------------

describe("StageSidebar props", () => {
  it("declares activeStage: PipelineStage prop", () => {
    expect(sourceCode).toMatch(/activeStage\s*:\s*PipelineStage/);
  });

  it("declares onStageSelect callback prop", () => {
    expect(sourceCode).toMatch(/onStageSelect\s*:\s*\(stage\s*:\s*PipelineStage\)\s*=>\s*void/);
  });
});

// ---------------------------------------------------------------------------
// 3. STAGE_CONFIG constant — all 10 stages
// ---------------------------------------------------------------------------

describe("STAGE_CONFIG constant", () => {
  it("defines STAGE_CONFIG as Array<{ stage: PipelineStage; label: string; number: number }>", () => {
    expect(sourceCode).toMatch(/STAGE_CONFIG\s*:\s*Array\s*<\s*\{/);
    expect(sourceCode).toMatch(/stage\s*:\s*PipelineStage/);
    expect(sourceCode).toMatch(/label\s*:\s*string/);
    expect(sourceCode).toMatch(/number\s*:\s*number/);
  });

  it("has exactly 10 stage entries", () => {
    const stageMatches = sourceCode.match(/\{\s*stage:\s*'[^']+',\s*label:\s*'[^']+',\s*number:\s*\d+\s*\}/g);
    expect(stageMatches).not.toBeNull();
    expect(stageMatches!.length).toBe(10);
  });

  it("includes setup stage with label Setup and number 1", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'setup',\s*label:\s*'Setup',\s*number:\s*1\s*\}/);
  });

  it("includes script stage with label Script and number 2", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'script',\s*label:\s*'Script',\s*number:\s*2\s*\}/);
  });

  it("includes tts-script stage with label TTS Script and number 3", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'tts-script',\s*label:\s*'TTS Script',\s*number:\s*3\s*\}/);
  });

  it("includes tts-render stage with label TTS Render and number 4", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'tts-render',\s*label:\s*'TTS Render',\s*number:\s*4\s*\}/);
  });

  it("includes audio-sync stage with label Audio Sync and number 5", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'audio-sync',\s*label:\s*'Audio Sync',\s*number:\s*5\s*\}/);
  });

  it("includes specs stage with label Spec Gen and number 6", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'specs',\s*label:\s*'Spec Gen',\s*number:\s*6\s*\}/);
  });

  it("includes veo stage with label Veo Gen and number 7", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'veo',\s*label:\s*'Veo Gen',\s*number:\s*7\s*\}/);
  });

  it("includes compositions stage with label Compositions and number 8", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'compositions',\s*label:\s*'Compositions',\s*number:\s*8\s*\}/);
  });

  it("includes render stage with label Render and number 9", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'render',\s*label:\s*'Render',\s*number:\s*9\s*\}/);
  });

  it("includes audit stage with label Audit and number 10", () => {
    expect(sourceCode).toMatch(/\{\s*stage:\s*'audit',\s*label:\s*'Audit',\s*number:\s*10\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 4. Status badge icons and classes
// ---------------------------------------------------------------------------

describe("status badge icons", () => {
  it("uses ● icon for done status", () => {
    expect(sourceCode).toMatch(/'●'/);
  });

  it("uses ◌ icon for running status", () => {
    expect(sourceCode).toMatch(/'◌'/);
  });

  it("uses ✕ icon for error status", () => {
    expect(sourceCode).toMatch(/'✕'/);
  });

  it("uses ○ icon for not_started status", () => {
    expect(sourceCode).toMatch(/'○'/);
  });
});

describe("status badge CSS classes", () => {
  it("applies text-stage-done for done status", () => {
    expect(sourceCode).toMatch(/['"]text-stage-done['"]/);
  });

  it("applies text-stage-running animate-stage-running for running status", () => {
    expect(sourceCode).toMatch(/['"]text-stage-running animate-stage-running['"]/);
  });

  it("applies text-stage-error for error status", () => {
    expect(sourceCode).toMatch(/['"]text-stage-error['"]/);
  });

  it("applies text-stage-not-started for not_started status", () => {
    expect(sourceCode).toMatch(/['"]text-stage-not-started['"]/);
  });
});

// ---------------------------------------------------------------------------
// 5. Active stage highlighting
// ---------------------------------------------------------------------------

describe("active stage highlighting", () => {
  it("applies border-l-2 to active stage", () => {
    expect(sourceCode).toMatch(/border-l-2/);
  });

  it("applies border-blue-400 to active stage", () => {
    expect(sourceCode).toMatch(/border-blue-400/);
  });

  it("applies bg-white/5 to active stage", () => {
    expect(sourceCode).toMatch(/bg-white\/5/);
  });

  it("checks isActive based on stage === activeStage", () => {
    expect(sourceCode).toMatch(/stage\s*===\s*activeStage/);
  });
});

// ---------------------------------------------------------------------------
// 6. Polling — GET /api/pipeline/status every 5 seconds
// ---------------------------------------------------------------------------

describe("status polling", () => {
  it("fetches /api/pipeline/status", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/status['"]\s*\)/);
  });

  it("uses setInterval with 5000ms interval", () => {
    expect(sourceCode).toMatch(/setInterval\s*\(\s*\(\)\s*=>\s*fetchStatus\(\)\s*,\s*5000\s*\)/);
  });

  it("clears interval on cleanup", () => {
    expect(sourceCode).toMatch(/clearInterval\s*\(\s*interval\s*\)/);
  });

  it("calls fetchStatus immediately on mount", () => {
    // fetchStatus() is called before polling is conditionally disabled/enabled
    expect(sourceCode).toMatch(/fetchStatus\(\)\s*;\s*\n\s*if\s*\(\s*disablePolling\s*\)/);
  });

  it("tracks polling mode in the useEffect dependency array", () => {
    expect(sourceCode).toMatch(
      /useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?\}\s*,\s*\[\s*disablePolling\s*\]\s*\)/
    );
  });

  it("updates state without flicker using spread merge", () => {
    expect(sourceCode).toMatch(/setStageStatuses\s*\(\s*\(prev\)\s*=>\s*\(\{[\s\S]*?\.\.\.prev[\s\S]*?\.\.\.data[\s\S]*?\}\)\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 7. Initial state defaults to not_started
// ---------------------------------------------------------------------------

describe("initial state", () => {
  it("initializes all stages to not_started status", () => {
    expect(sourceCode).toMatch(/status:\s*'not_started'/);
  });

  it("uses useState with initStatuses function", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*Record\s*<[\s\S]*?>\s*>\s*\(\s*initStatuses\s*\)/);
  });

  it("defines stageStatuses state as Record<PipelineStage, StageStatusEntry>", () => {
    expect(sourceCode).toMatch(/Record\s*<\s*PipelineStage\s*,\s*StageStatusEntry\s*>/);
  });
});

// ---------------------------------------------------------------------------
// 8. Error tooltip — HTML title attribute
// ---------------------------------------------------------------------------

describe("error tooltip", () => {
  it("sets title attribute on badge for error status", () => {
    expect(sourceCode).toMatch(/title=\{status\s*===\s*'error'\s*\?\s*entry\.error\s*\|\|\s*'Error'\s*:\s*undefined\}/);
  });

  it("sets title attribute on row for error status", () => {
    expect(sourceCode).toMatch(/title=\{entry\?\.status\s*===\s*'error'\s*\?\s*entry\.error\s*\|\|\s*'Error'\s*:\s*undefined\}/);
  });
});

// ---------------------------------------------------------------------------
// 9. Sidebar container styling
// ---------------------------------------------------------------------------

describe("sidebar container", () => {
  it("uses aside element", () => {
    expect(sourceCode).toMatch(/<aside/);
  });

  it("has correct container className", () => {
    expect(sourceCode).toMatch(/className="flex flex-col w-48 bg-sidebar border-r border-border h-screen"/);
  });
});

// ---------------------------------------------------------------------------
// 10. Row styling
// ---------------------------------------------------------------------------

describe("row styling", () => {
  it("renders stage rows as buttons", () => {
    expect(sourceCode).toMatch(/<button/);
    expect(sourceCode).toMatch(/type="button"/);
  });

  it("applies cursor-pointer to each row", () => {
    expect(sourceCode).toMatch(/cursor-pointer/);
  });

  it("applies px-3 py-2 padding to each row", () => {
    expect(sourceCode).toMatch(/px-3 py-2/);
  });

  it("applies flex items-center gap-2 layout", () => {
    expect(sourceCode).toMatch(/flex items-center gap-2/);
  });

  it("applies hover:bg-white/5 transition-colors to rows", () => {
    expect(sourceCode).toMatch(/hover:bg-white\/5 transition-colors/);
  });

  it("renders stage number in a span", () => {
    expect(sourceCode).toMatch(/text-xs text-muted-foreground w-6/);
  });

  it("renders stage label in a flex-1 span", () => {
    expect(sourceCode).toMatch(/flex-1 text-sm/);
  });
});

// ---------------------------------------------------------------------------
// 11. Click handling
// ---------------------------------------------------------------------------

describe("click handling", () => {
  it("calls onStageSelect with the stage on click", () => {
    expect(sourceCode).toMatch(/onClick=\{\(\)\s*=>\s*onStageSelect\(stage\)\}/);
  });

  it("marks the active stage with aria-current=step", () => {
    expect(sourceCode).toMatch(/aria-current=\{isActive\s*\?\s*'step'\s*:\s*undefined\}/);
  });
});

// ---------------------------------------------------------------------------
// 12. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React, useEffect, useState from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,\s*\{\s*useEffect\s*,\s*useState\s*\}\s*from\s+['"]react['"]/);
  });

  it("imports PipelineStage and StageStatus types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{\s*PipelineStage\s*,\s*StageStatus\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 13. Export shape
// ---------------------------------------------------------------------------

describe("export shape", () => {
  it("exports StageSidebar as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+StageSidebar/);
  });
});

// ---------------------------------------------------------------------------
// 14. StageStatusEntry type
// ---------------------------------------------------------------------------

describe("StageStatusEntry type", () => {
  it("defines StageStatusEntry with status: StageStatus", () => {
    expect(sourceCode).toMatch(/type\s+StageStatusEntry\s*=\s*\{[\s\S]*?status\s*:\s*StageStatus/);
  });

  it("defines optional error field", () => {
    expect(sourceCode).toMatch(/error\?\s*:\s*string\s*\|\s*null/);
  });
});

// ---------------------------------------------------------------------------
// 15. Fetch error handling — retains last known state
// ---------------------------------------------------------------------------

describe("fetch error handling", () => {
  it("swallows fetch errors silently", () => {
    expect(sourceCode).toMatch(/catch\s*\{[\s\S]*?\/\/\s*Swallow errors/);
  });

  it("uses mounted flag to prevent state updates after unmount", () => {
    expect(sourceCode).toMatch(/let\s+mounted\s*=\s*true/);
    expect(sourceCode).toMatch(/if\s*\(\s*!mounted\s*\)\s*return/);
    expect(sourceCode).toMatch(/mounted\s*=\s*false/);
  });

  it("returns early if response is not ok", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*return/);
  });
});

// ---------------------------------------------------------------------------
// 16. Module-level structure checks
// ---------------------------------------------------------------------------

describe("module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("is a TypeScript React file", () => {
    expect(SOURCE_PATH).toMatch(/\.tsx$/);
  });

  it("does not use SWR or React Query", () => {
    expect(sourceCode).not.toMatch(/import.*from\s+['"]swr['"]/);
    expect(sourceCode).not.toMatch(/import.*from\s+['"]@tanstack\/react-query['"]/);
    expect(sourceCode).not.toMatch(/import.*from\s+['"]react-query['"]/);
  });

  it("uses simple fetch for polling", () => {
    expect(sourceCode).toMatch(/fetch\s*\(/);
  });
});
