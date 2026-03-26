/**
 * Tests for components/stages/Stage5AudioSync.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/stage5_audio_sync_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: onAdvance: () => void.
 *   2. Top section: section grouping table with inline-editable segment ranges. [Save Config] PUTs audioSync.sectionGroups to /api/project.
 *   3. [Run Audio Sync] button: POSTs to /api/pipeline/audio-sync/run. Shows SseLogPanel with returned jobId.
 *   4. Bottom section: Word Timestamp Viewer — columns: word, start (3dp), end (3dp), segmentId. Section filter dropdown. Search input.
 *   5. Virtual scrolling for large timestamp lists: CSS contain: strict with fixed row heights.
 *   6. Load timestamps: GET /api/pipeline/audio-sync/timestamps?section={sectionId}.
 *   7. 'use client' directive.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "stages", "Stage5AudioSync.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive (Req 7)
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

  it("exports Stage5AudioSync as default export", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+Stage5AudioSync/);
  });
});

// ---------------------------------------------------------------------------
// 3. Props interface (Req 1)
// ---------------------------------------------------------------------------

describe("Stage5AudioSync props", () => {
  it("declares onAdvance: () => void prop", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines Stage5AudioSyncProps interface", () => {
    expect(sourceCode).toMatch(/interface\s+Stage5AudioSyncProps/);
  });

  it("destructures onAdvance from props", () => {
    expect(sourceCode).toMatch(/\{\s*onAdvance\s*\}\s*:\s*Stage5AudioSyncProps/);
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

  it("imports useRef from react", () => {
    expect(sourceCode).toMatch(/useRef/);
  });

  it("imports ProjectConfig and Section types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{[^}]*ProjectConfig[^}]*\}/);
    expect(sourceCode).toMatch(/import\s+type\s*\{[^}]*Section[^}]*\}/);
  });

  it("imports SseLogPanel", () => {
    expect(sourceCode).toMatch(/import\s+SseLogPanel\s+from/);
  });
});

// ---------------------------------------------------------------------------
// 5. Type definitions
// ---------------------------------------------------------------------------

describe("type definitions", () => {
  it("defines WordTimestamp interface", () => {
    expect(sourceCode).toMatch(/interface\s+WordTimestamp/);
  });

  it("defines SegmentValidation interface", () => {
    expect(sourceCode).toMatch(/interface\s+SegmentValidation/);
  });

  it("defines SegmentValidationSummary interface", () => {
    expect(sourceCode).toMatch(/interface\s+SegmentValidationSummary/);
  });

  it("WordTimestamp has word: string property", () => {
    // Match inside the interface block
    expect(sourceCode).toMatch(/interface\s+WordTimestamp[\s\S]*?word\s*:\s*string/);
  });

  it("WordTimestamp has start: number property", () => {
    expect(sourceCode).toMatch(/interface\s+WordTimestamp[\s\S]*?start\s*:\s*number/);
  });

  it("WordTimestamp has end: number property", () => {
    expect(sourceCode).toMatch(/interface\s+WordTimestamp[\s\S]*?end\s*:\s*number/);
  });

  it("WordTimestamp has segmentId property", () => {
    expect(sourceCode).toMatch(/interface\s+WordTimestamp[\s\S]*?segmentId/);
  });
});

// ---------------------------------------------------------------------------
// 6. Virtual scrolling constants (Req 5)
// ---------------------------------------------------------------------------

describe("virtual scrolling constants", () => {
  it("defines ROW_HEIGHT constant", () => {
    expect(sourceCode).toMatch(/const\s+ROW_HEIGHT\s*=\s*\d+/);
  });

  it("defines VIEWPORT_HEIGHT constant", () => {
    expect(sourceCode).toMatch(/const\s+VIEWPORT_HEIGHT\s*=\s*\d+/);
  });
});

// ---------------------------------------------------------------------------
// 7. State management
// ---------------------------------------------------------------------------

describe("state management", () => {
  it("tracks project state as ProjectConfig | null", () => {
    expect(sourceCode).toMatch(/\[\s*project\s*,\s*setProject\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*ProjectConfig\s*\|\s*null\s*>/);
  });

  it("tracks loadingProject state", () => {
    expect(sourceCode).toMatch(/\[\s*loadingProject\s*,\s*setLoadingProject\s*\]/);
  });

  it("tracks projectError state", () => {
    expect(sourceCode).toMatch(/\[\s*projectError\s*,\s*setProjectError\s*\]/);
  });

  it("tracks sectionGroups state as Record<string, string[]>", () => {
    expect(sourceCode).toMatch(/\[\s*sectionGroups\s*,\s*setSectionGroups\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*Record\s*<\s*string\s*,\s*string\[\]\s*>\s*>/);
  });

  it("tracks savingConfig state", () => {
    expect(sourceCode).toMatch(/\[\s*savingConfig\s*,\s*setSavingConfig\s*\]/);
  });

  it("tracks jobId state as string | null", () => {
    expect(sourceCode).toMatch(/\[\s*jobId\s*,\s*setJobId\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*string\s*\|\s*null\s*>/);
  });

  it("tracks selectedSectionId state", () => {
    expect(sourceCode).toMatch(/\[\s*selectedSectionId\s*,\s*setSelectedSectionId\s*\]/);
  });

  it("tracks timestamps state as WordTimestamp[]", () => {
    expect(sourceCode).toMatch(/\[\s*timestamps\s*,\s*setTimestamps\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*WordTimestamp\[\]\s*>/);
  });

  it("tracks validationRows state as SegmentValidation[]", () => {
    expect(sourceCode).toMatch(/\[\s*validationRows\s*,\s*setValidationRows\s*\]/);
    expect(sourceCode).toMatch(/useState\s*<\s*SegmentValidation\[\]\s*>/);
  });

  it("tracks validationSummary state", () => {
    expect(sourceCode).toMatch(/\[\s*validationSummary\s*,\s*setValidationSummary\s*\]/);
  });

  it("tracks audio-sync artifact freshness state", () => {
    expect(sourceCode).toMatch(/\[\s*artifactState\s*,\s*setArtifactState\s*\]/);
  });

  it("uses a stable empty sections fallback before project load", () => {
    expect(sourceCode).toMatch(/const\s+EMPTY_SECTIONS\s*:\s*Section\[\]\s*=\s*\[\]/);
    expect(sourceCode).toMatch(/project\?\.sections\s*\?\?\s*EMPTY_SECTIONS/);
  });

  it("tracks per-segment rerender job IDs", () => {
    expect(sourceCode).toMatch(/\[\s*validationJobIds\s*,\s*setValidationJobIds\s*\]/);
  });

  it("tracks per-segment audio-sync job IDs", () => {
    expect(sourceCode).toMatch(/\[\s*validationSyncJobIds\s*,\s*setValidationSyncJobIds\s*\]/);
  });

  it("tracks threshold percent and max-retry state for batch transcript retries", () => {
    expect(sourceCode).toMatch(/\[\s*retryMatchThresholdPercent\s*,\s*setRetryMatchThresholdPercent\s*\]/);
    expect(sourceCode).toMatch(/\[\s*retryMaxAttempts\s*,\s*setRetryMaxAttempts\s*\]/);
  });

  it("tracks batch retry job IDs", () => {
    expect(sourceCode).toMatch(/\[\s*batchValidationRerenderJobId\s*,\s*setBatchValidationRerenderJobId\s*\]/);
    expect(sourceCode).toMatch(/\[\s*batchValidationSyncJobId\s*,\s*setBatchValidationSyncJobId\s*\]/);
  });

  it("tracks playingSegmentId state for validation audio preview", () => {
    expect(sourceCode).toMatch(/\[\s*playingSegmentId\s*,\s*setPlayingSegmentId\s*\]/);
  });

  it("tracks loadingTimestamps state", () => {
    expect(sourceCode).toMatch(/\[\s*loadingTimestamps\s*,\s*setLoadingTimestamps\s*\]/);
  });

  it("tracks search state", () => {
    expect(sourceCode).toMatch(/\[\s*search\s*,\s*setSearch\s*\]/);
  });

  it("tracks scrollTop state for virtual scrolling", () => {
    expect(sourceCode).toMatch(/\[\s*scrollTop\s*,\s*setScrollTop\s*\]/);
  });

  it("has scrollRef for scroll container", () => {
    expect(sourceCode).toMatch(/scrollRef\s*=\s*useRef/);
  });
});

// ---------------------------------------------------------------------------
// 8. Project config loading on mount (Req 2, 4)
// ---------------------------------------------------------------------------

describe("project config loading on mount", () => {
  it("fetches project from GET /api/project", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project['"]\s*\)/);
  });

  it("sets project state from response", () => {
    expect(sourceCode).toMatch(/setProject\s*\(\s*data\s*\)/);
  });

  it("initializes sectionGroups from project audioSync config (normalized)", () => {
    expect(sourceCode).toMatch(/setSectionGroups\s*\(\s*normalized\s*\)/);
  });

  it("sets default selectedSectionId to first section", () => {
    expect(sourceCode).toMatch(/setSelectedSectionId\s*\(\s*data\.sections\[0\]\.id\s*\)/);
  });

  it("handles loading state correctly", () => {
    expect(sourceCode).toMatch(/setLoadingProject\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setLoadingProject\s*\(\s*false\s*\)/);
  });

  it("handles fetch errors", () => {
    expect(sourceCode).toMatch(/setProjectError/);
  });

  it("uses cleanup flag to prevent state updates on unmount", () => {
    expect(sourceCode).toMatch(/let\s+active\s*=\s*true/);
    expect(sourceCode).toMatch(/active\s*=\s*false/);
  });
});

// ---------------------------------------------------------------------------
// 9. Timestamp loading when section changes (Req 6)
// ---------------------------------------------------------------------------

describe("timestamp loading", () => {
  it("fetches timestamps from GET /api/pipeline/audio-sync/timestamps with section param", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*[\s\S]*?\/api\/pipeline\/audio-sync\/timestamps\?section=/);
  });

  it("encodes section ID in URL", () => {
    expect(sourceCode).toMatch(/encodeURIComponent\s*\(\s*[\s\S]*?selectedSectionId/);
  });

  it("sets timestamps from response (unwrapping wrapped JSON)", () => {
    expect(sourceCode).toMatch(/setTimestamps\s*\(\s*list\s*\)/);
  });

  it("sets validationRows from response validation payload", () => {
    expect(sourceCode).toMatch(/setValidationRows\s*\(\s*Array\.isArray\s*\(\s*data\?\.validation\?\.segments\s*\)/);
  });

  it("sets validationSummary from response validation payload", () => {
    expect(sourceCode).toMatch(/setValidationSummary\s*\(\s*data\?\.validation\?\.summary/);
  });

  it("reads artifactState from the timestamps response", () => {
    expect(sourceCode).toMatch(/data\?\.artifactState/);
    expect(sourceCode).toMatch(/setArtifactState\s*\(\s*nextArtifactState\s*\)/);
  });

  it("clears stale timestamps but preserves the last validation rows when audio sync data is stale", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*nextArtifactState\.stale\s*\)/);
    expect(sourceCode).toMatch(/setTimestamps\s*\(\s*\[\]\s*\)/);
    expect(sourceCode).toMatch(/setValidationRows\s*\(\s*nextValidationRows\s*\)/);
    expect(sourceCode).toMatch(/setValidationSummary\s*\(\s*nextValidationSummary\s*\)/);
  });

  it("tracks loading state for timestamps", () => {
    expect(sourceCode).toMatch(/setLoadingTimestamps\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setLoadingTimestamps\s*\(\s*false\s*\)/);
  });

  it("clears timestamps on fetch error", () => {
    expect(sourceCode).toMatch(/catch[\s\S]*?setTimestamps\s*\(\s*\[\]\s*\)/);
  });

  it("depends on selectedSectionId", () => {
    expect(sourceCode).toMatch(/\[\s*dataReloadVersion\s*,\s*selectedSectionId\s*\]/);
  });

  it("returns early if no selectedSectionId", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!selectedSectionId\s*\)\s*return/);
  });
});

// ---------------------------------------------------------------------------
// 10. Transcript validation panel
// ---------------------------------------------------------------------------

describe("transcript validation panel", () => {
  it("renders a flagged transcript mismatch section", () => {
    expect(sourceCode).toMatch(/Flagged Transcript Mismatches/);
  });

  it("renders a stale audio-sync warning when sync outputs are older than TTS audio", () => {
    expect(sourceCode).toMatch(/Audio sync data is stale relative to the current TTS audio/);
    expect(sourceCode).toMatch(/Showing the last available transcript validation results/);
    expect(sourceCode).toMatch(/artifactState\.stale/);
  });

  it("filters validation rows to warn/fail mismatches", () => {
    expect(sourceCode).toMatch(/validationRows\.filter\s*\(\s*\(row\)\s*=>\s*row\.status\s*!==\s*['"]pass['"]/);
  });

  it("shows expected and actual transcript columns", () => {
    expect(sourceCode).toMatch(/Expected Text/);
    expect(sourceCode).toMatch(/Actual Transcript/);
  });

  it("renders a Re-render Segment action", () => {
    expect(sourceCode).toMatch(/Re-render Segment/);
  });

  it("renders a Play Audio action", () => {
    expect(sourceCode).toMatch(/Play Audio/);
  });

  it("renders controls for batch retry threshold and retry count", () => {
    expect(sourceCode).toMatch(/Retry Below Match %/);
    expect(sourceCode).toMatch(/Max Retries/);
    expect(sourceCode).toMatch(/Retry Flagged Segments/);
    expect(sourceCode).toMatch(/Retry Across All Sections/);
  });

  it("shows a current-section below-threshold summary", () => {
    expect(sourceCode).toMatch(/Below Threshold in This Section/);
    expect(sourceCode).toMatch(/retryableValidationSegmentIds\.length/);
    expect(sourceCode).toMatch(/belowThresholdValidationRows/);
  });

  it("shows a project-wide below-threshold summary with expandable breakdown", () => {
    expect(sourceCode).toMatch(/Below Threshold Across Project/);
    expect(sourceCode).toMatch(/projectWideRetryableSegmentIdsBySection/);
    expect(sourceCode).toMatch(/projectWideRetryableSectionIds/);
    expect(sourceCode).toMatch(/<details/);
  });

  it("shows retry progress while a batch rerender is running", () => {
    expect(sourceCode).toMatch(/Retry Progress/);
    expect(sourceCode).toMatch(/batchRetryProgress/);
    expect(sourceCode).toMatch(/attempt\}/);
  });

  it("shows a preparing retry phase before downstream jobs start", () => {
    expect(sourceCode).toMatch(/phase:\s*'preparing'/);
    expect(sourceCode).toMatch(/Preparing retry run/);
  });

  it("styles retry actions as explicit buttons", () => {
    expect(sourceCode).toMatch(/inline-flex items-center justify-center/);
    expect(sourceCode).toMatch(/shadow-sm/);
    expect(sourceCode).toMatch(/hover:bg-orange-500/);
    expect(sourceCode).toMatch(/hover:bg-indigo-500/);
  });

  it("reports before and after below-threshold counts after retry runs", () => {
    expect(sourceCode).toMatch(/Before:/);
    expect(sourceCode).toMatch(/After:/);
  });
});

// ---------------------------------------------------------------------------
// 11. Transcript rerender action
// ---------------------------------------------------------------------------

describe("transcript rerender action", () => {
  it("posts flagged segment IDs to /api/pipeline/tts-render/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/tts-render\/run['"]/);
    expect(sourceCode).toMatch(/body\s*:\s*JSON\.stringify\(\s*\{[\s\S]*segments\s*:\s*\[\s*segmentId\s*\][\s\S]*skipDependencies\s*:\s*true[\s\S]*\}\s*\)/);
  });

  it("extracts a rerender job ID from the SSE response", () => {
    expect(sourceCode).toMatch(/extractJobIdFromSse/);
  });

  it("renders an SseLogPanel for per-segment rerender jobs", () => {
    expect(sourceCode).toMatch(/<SseLogPanel[\s\S]*?jobId=\{validationJobIds\[row\.segmentId\] \?\? null\}/);
  });

  it("runs audio sync again for the selected section after rerender completes", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/audio-sync\/run['"]/);
    expect(sourceCode).toMatch(/body\s*:\s*JSON\.stringify\(\s*\{[\s\S]*sections\s*:\s*\[\s*selectedSectionId\s*\][\s\S]*allowValidationFailures\s*:\s*true[\s\S]*skipDependencies\s*:\s*true[\s\S]*\}\s*\)/);
  });

  it("renders an SseLogPanel for follow-up audio sync jobs", () => {
    expect(sourceCode).toMatch(/<SseLogPanel[\s\S]*?jobId=\{validationSyncJobIds\[row\.segmentId\] \?\? null\}/);
  });

  it("delegates batch retries to the shared retry helper", () => {
    expect(sourceCode).toMatch(/runFlaggedTranscriptRerenderRetries/);
    expect(sourceCode).toMatch(/collectFlaggedSegmentsBelowThreshold/);
    expect(sourceCode).toMatch(/runFlaggedTranscriptRerenderRetriesAcrossSections/);
    expect(sourceCode).toMatch(/collectFlaggedSegmentsBelowThresholdBySection/);
  });

  it("allows retry flows to continue after audio-sync validation errors", () => {
    expect(sourceCode).toMatch(/continueOnAudioSyncError:\s*true/);
    expect(sourceCode).toMatch(/allowValidationFailures:\s*true/);
    expect(sourceCode).toMatch(/skipDependencies:\s*true/);
  });

  it("loads validation rows across sections for the project-wide threshold summary", () => {
    expect(sourceCode).toMatch(/setAllValidationRowsBySection/);
    expect(sourceCode).toMatch(/loadingAllValidationRows/);
    expect(sourceCode).toMatch(/fetchValidationRowsForSection/);
  });

  it("includes the selected section's last available validation rows in project-wide retry summaries even when stale", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*section\.id\s*===\s*selectedSectionId\s*\)\s*\{\s*return\s*\[[\s\S]*?rows\s*:\s*validationRows/);
  });

  it("shows when the project-wide retry summary includes stale sections", () => {
    expect(sourceCode).toMatch(/Includes last available validation results for/);
  });

  it("avoids resetting project-wide validation state on every pre-load render", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*sections\.length\s*===\s*0\s*\)/);
    expect(sourceCode).toMatch(/setAllValidationRowsBySection\s*\(\s*\(prev\)\s*=>/);
    expect(sourceCode).toMatch(/Object\.keys\s*\(\s*prev\s*\)\.length\s*===\s*0\s*\?\s*prev\s*:\s*\{\s*\}/);
  });

  it("renders SseLogPanels for batch rerender and batch audio-sync jobs", () => {
    expect(sourceCode).toMatch(/<SseLogPanel[\s\S]*?jobId=\{batchValidationRerenderJobId\}/);
    expect(sourceCode).toMatch(/<SseLogPanel[\s\S]*?jobId=\{batchValidationSyncJobId\}/);
  });
});

// ---------------------------------------------------------------------------
// 12. Transcript audio preview action
// ---------------------------------------------------------------------------

describe("transcript audio preview action", () => {
  it("defines handlePreviewSegmentAudio", () => {
    expect(sourceCode).toMatch(/const\s+handlePreviewSegmentAudio\s*=\s*async/);
  });

  it("uses the preview audio element ref for the segment wav route", () => {
    expect(sourceCode).toMatch(/const\s+audio\s*=\s*previewAudioRef\.current/);
    expect(sourceCode).toMatch(/loadSegmentPreviewAudio\s*\(/);
    expect(sourceCode).toMatch(/previewAudioObjectUrlRef/);
  });

  it("toggles stop/play based on the active segment", () => {
    expect(sourceCode).toMatch(/playingSegmentId\s*===\s*segmentId/);
    expect(sourceCode).toMatch(/playingSegmentId\s*===\s*row\.segmentId\s*\?\s*'Stop Audio'\s*:\s*'Play Audio'/);
  });

  it("renders a hidden audio element for preview playback", () => {
    expect(sourceCode).toMatch(/<audio[\s\S]*?ref=\{previewAudioRef\}/);
    expect(sourceCode).toMatch(/preload="auto"/);
  });

  it("cleans up preview audio blob URLs on teardown", () => {
    expect(sourceCode).toMatch(/resetSegmentPreviewAudio\s*\(/);
  });
});

// ---------------------------------------------------------------------------
// 13. Word filtering via search (Req 4 — search input)
// ---------------------------------------------------------------------------

describe("word filtering", () => {
  it("uses useMemo for filteredWords", () => {
    expect(sourceCode).toMatch(/filteredWords\s*=\s*useMemo/);
  });

  it("filters by word text case-insensitively", () => {
    expect(sourceCode).toMatch(/w\.word\.toLowerCase\s*\(\s*\)\.includes\s*\(\s*term\s*\)/);
  });

  it("converts search term to lowercase", () => {
    expect(sourceCode).toMatch(/search\.toLowerCase\s*\(\s*\)/);
  });

  it("depends on timestamps and search state", () => {
    expect(sourceCode).toMatch(/\[\s*timestamps\s*,\s*search\s*\]/);
  });
});

// ---------------------------------------------------------------------------
// 11. Virtual scrolling computation (Req 5)
// ---------------------------------------------------------------------------

describe("virtual scrolling computation", () => {
  it("computes totalWords from timestamps length", () => {
    expect(sourceCode).toMatch(/totalWords\s*=\s*timestamps\.length/);
  });

  it("computes visible count from viewport and row height", () => {
    expect(sourceCode).toMatch(/visibleCount\s*=\s*Math\.ceil\s*\(\s*VIEWPORT_HEIGHT\s*\/\s*ROW_HEIGHT\s*\)/);
  });

  it("computes startIndex from scrollTop and row height", () => {
    expect(sourceCode).toMatch(/startIndex\s*=\s*Math\.max\s*\(\s*0\s*,\s*Math\.floor\s*\(\s*scrollTop\s*\/\s*ROW_HEIGHT\s*\)/);
  });

  it("computes endIndex capped by filteredWords length", () => {
    expect(sourceCode).toMatch(/endIndex\s*=\s*Math\.min\s*\(\s*filteredWords\.length/);
  });

  it("slices visible words from filteredWords", () => {
    expect(sourceCode).toMatch(/visibleWords\s*=\s*filteredWords\.slice\s*\(\s*startIndex\s*,\s*endIndex\s*\)/);
  });

  it("computes offsetY for translateY", () => {
    expect(sourceCode).toMatch(/offsetY\s*=\s*startIndex\s*\*\s*ROW_HEIGHT/);
  });

  it("computes totalHeight for container", () => {
    expect(sourceCode).toMatch(/totalHeight\s*=\s*filteredWords\.length\s*\*\s*ROW_HEIGHT/);
  });
});

// ---------------------------------------------------------------------------
// 12. Section grouping edit handler (Req 2)
// ---------------------------------------------------------------------------

describe("section grouping edit handler", () => {
  it("defines handleGroupChange function", () => {
    expect(sourceCode).toMatch(/const\s+handleGroupChange\s*=/);
  });

  it("splits comma-separated input into segments", () => {
    expect(sourceCode).toMatch(/value[\s\S]*?\.split\s*\(\s*['"],['"]?\s*\)/);
  });

  it("trims whitespace from segment IDs", () => {
    expect(sourceCode).toMatch(/\.map\s*\(\s*\(s\)\s*=>\s*s\.trim\s*\(\s*\)\s*\)/);
  });

  it("filters out empty strings", () => {
    expect(sourceCode).toMatch(/\.filter\s*\(\s*Boolean\s*\)/);
  });

  it("updates sectionGroups state", () => {
    expect(sourceCode).toMatch(/setSectionGroups\s*\(\s*\(prev\)\s*=>\s*\(\s*\{\s*\.\.\.prev\s*,\s*\[sectionId\]\s*:\s*segments\s*\}\s*\)\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. Save Config handler (Req 2)
// ---------------------------------------------------------------------------

describe("save config handler", () => {
  it("defines handleSaveConfig as async function", () => {
    expect(sourceCode).toMatch(/const\s+handleSaveConfig\s*=\s*async/);
  });

  it("PUTs to /api/project", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project['"]\s*,/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]PUT['"]/);
  });

  it("sends Content-Type: application/json header", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]application\/json['"]/);
  });

  it("sends audioSync.sectionGroups in body", () => {
    expect(sourceCode).toMatch(/audioSync\s*:\s*\{[\s\S]*?sectionGroups/);
  });

  it("tracks saving state", () => {
    expect(sourceCode).toMatch(/setSavingConfig\s*\(\s*true\s*\)/);
    expect(sourceCode).toMatch(/setSavingConfig\s*\(\s*false\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Run Audio Sync handler (Req 3)
// ---------------------------------------------------------------------------

describe("run audio sync handler", () => {
  it("defines handleRunAudioSync as async function", () => {
    expect(sourceCode).toMatch(/const\s+handleRunAudioSync\s*=\s*async/);
  });

  it("POSTs to /api/pipeline/audio-sync/run", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/audio-sync\/run['"]\s*,/);
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("extracts jobId from response and sets state", () => {
    expect(sourceCode).toMatch(/extractJobIdFromSse/);
    expect(sourceCode).toMatch(/setJobId\s*\(\s*nextJobId\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 15. SSE done handler — auto-load timestamps (Req — after audio sync)
// ---------------------------------------------------------------------------

describe("SSE done handler", () => {
  it("defines handleSseDone function", () => {
    expect(sourceCode).toMatch(/const\s+handleSseDone\s*=/);
  });

  it("checks project sections exist", () => {
    expect(sourceCode).toMatch(/project\?\.sections\?\.length/);
  });

  it("sets selectedSectionId to first section when not already set", () => {
    expect(sourceCode).toMatch(/setSelectedSectionId\s*\(\s*project\.sections\[0\]\.id\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 16. SseLogPanel integration (Req 3)
// ---------------------------------------------------------------------------

describe("SseLogPanel integration", () => {
  it("renders SseLogPanel component", () => {
    expect(sourceCode).toMatch(/<SseLogPanel/);
  });

  it("passes jobId prop to SseLogPanel", () => {
    expect(sourceCode).toMatch(/jobId=\{jobId\}/);
  });

  it("passes onDone callback to SseLogPanel", () => {
    expect(sourceCode).toMatch(/onDone=\{handleSseDone\}/);
  });
});

// ---------------------------------------------------------------------------
// 17. Section grouping table rendering (Req 2)
// ---------------------------------------------------------------------------

describe("section grouping table", () => {
  it("renders section grouping header", () => {
    expect(sourceCode).toMatch(/Audio Sync Section Groups/);
  });

  it("renders Section column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Section<\/th>/);
  });

  it("renders Segment IDs column header", () => {
    expect(sourceCode).toMatch(/Segment IDs/);
  });

  it("maps sections to table rows", () => {
    expect(sourceCode).toMatch(/sections\.map\s*\(\s*\(section\)\s*=>/);
  });

  it("displays section label", () => {
    expect(sourceCode).toMatch(/section\.label/);
  });

  it("renders input for comma-separated segment IDs", () => {
    expect(sourceCode).toMatch(/<input[\s\S]*?value=\{[\s\S]*?sectionGroups\[section\.id\]/);
  });

  it("joins segment IDs with comma-space for display", () => {
    expect(sourceCode).toMatch(/\.join\s*\(\s*['"],\s*['"]\s*\)/);
  });

  it("handles input onChange for segment groups", () => {
    expect(sourceCode).toMatch(/onChange=\{[\s\S]*?handleGroupChange\s*\(\s*section\.id/);
  });

  it("includes placeholder for segment input", () => {
    expect(sourceCode).toMatch(/placeholder="segment1, segment2, segment3"/);
  });
});

// ---------------------------------------------------------------------------
// 18. Save Config button (Req 2)
// ---------------------------------------------------------------------------

describe("Save Config button", () => {
  it("renders Save Config button text", () => {
    expect(sourceCode).toMatch(/Save Config/);
  });

  it("button calls handleSaveConfig on click", () => {
    expect(sourceCode).toMatch(/onClick=\{handleSaveConfig\}/);
  });

  it("button is disabled while saving", () => {
    expect(sourceCode).toMatch(/disabled=\{savingConfig\}/);
  });

  it("shows Saving… text while saving", () => {
    expect(sourceCode).toMatch(/savingConfig\s*\?\s*['"]Saving…['"]\s*:\s*['"]Save Config['"]/);
  });
});

// ---------------------------------------------------------------------------
// 19. Run Audio Sync button (Req 3)
// ---------------------------------------------------------------------------

describe("Run Audio Sync button", () => {
  it("renders Run Audio Sync button text", () => {
    expect(sourceCode).toMatch(/Run Audio Sync/);
  });

  it("button calls handleRunAudioSync on click", () => {
    expect(sourceCode).toMatch(/onClick=\{handleRunAudioSync\}/);
  });

  it("uses emerald styling", () => {
    expect(sourceCode).toMatch(/bg-emerald-600/);
  });
});

// ---------------------------------------------------------------------------
// 20. Word Timestamp Viewer (Req 4)
// ---------------------------------------------------------------------------

describe("Word Timestamp Viewer", () => {
  it("renders Word Timestamp Viewer header", () => {
    expect(sourceCode).toMatch(/Word Timestamp Viewer/);
  });

  it("renders Word column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Word<\/th>/);
  });

  it("renders Start column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Start<\/th>/);
  });

  it("renders End column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>End<\/th>/);
  });

  it("renders Segment ID column header", () => {
    expect(sourceCode).toMatch(/<th[\s\S]*?>Segment ID<\/th>/);
  });

  it("displays word text in table cells", () => {
    expect(sourceCode).toMatch(/w\.word/);
  });

  it("formats start time to 3 decimal places", () => {
    expect(sourceCode).toMatch(/w\.start\.toFixed\s*\(\s*3\s*\)/);
  });

  it("formats end time to 3 decimal places", () => {
    expect(sourceCode).toMatch(/w\.end\.toFixed\s*\(\s*3\s*\)/);
  });

  it("displays segmentId with fallback to dash", () => {
    expect(sourceCode).toMatch(/w\.segmentId\s*\?\?\s*['"][-]['"]/);
  });

  it("maps visibleWords for table rows", () => {
    expect(sourceCode).toMatch(/visibleWords\.map/);
  });

  it("sets row height via style", () => {
    expect(sourceCode).toMatch(/height:\s*ROW_HEIGHT/);
  });
});

// ---------------------------------------------------------------------------
// 21. Section filter dropdown (Req 4)
// ---------------------------------------------------------------------------

describe("section filter dropdown", () => {
  it("renders Section label", () => {
    expect(sourceCode).toMatch(/Section:/);
  });

  it("renders select element for section filter", () => {
    expect(sourceCode).toMatch(/<select/);
  });

  it("select value is bound to selectedSectionId", () => {
    expect(sourceCode).toMatch(/value=\{selectedSectionId\}/);
  });

  it("select onChange updates selectedSectionId", () => {
    expect(sourceCode).toMatch(/onChange=\{[\s\S]*?setSelectedSectionId\s*\(\s*e\.target\.value\s*\)/);
  });

  it("maps sections to option elements", () => {
    expect(sourceCode).toMatch(/sections\.map\s*\(\s*\(s\)\s*=>/);
    expect(sourceCode).toMatch(/<option[\s\S]*?value=\{s\.id\}/);
  });

  it("displays section label in option", () => {
    expect(sourceCode).toMatch(/s\.label/);
  });
});

// ---------------------------------------------------------------------------
// 22. Search input (Req 4)
// ---------------------------------------------------------------------------

describe("search input", () => {
  it("renders search input with placeholder", () => {
    expect(sourceCode).toMatch(/placeholder=["']Search word/);
  });

  it("search input value is bound to search state", () => {
    expect(sourceCode).toMatch(/value=\{search\}/);
  });

  it("search input onChange updates search state", () => {
    expect(sourceCode).toMatch(/onChange=\{[\s\S]*?setSearch\s*\(\s*e\.target\.value\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 23. Word count display (Req — word count)
// ---------------------------------------------------------------------------

describe("word count display", () => {
  it("displays filteredWords.length", () => {
    expect(sourceCode).toMatch(/filteredWords\.length/);
  });

  it("displays totalWords count", () => {
    expect(sourceCode).toMatch(/totalWords/);
  });

  it("shows 'of' between filtered and total count", () => {
    expect(sourceCode).toMatch(/\{filteredWords\.length\}\s*of\s*\{totalWords\}\s*words/);
  });
});

// ---------------------------------------------------------------------------
// 24. Virtual scrolling DOM structure (Req 5)
// ---------------------------------------------------------------------------

describe("virtual scrolling DOM structure", () => {
  it("uses CSS contain: strict on scroll container", () => {
    expect(sourceCode).toMatch(/contain:\s*['"]strict['"]/);
  });

  it("sets scroll container height to VIEWPORT_HEIGHT", () => {
    expect(sourceCode).toMatch(/height:\s*VIEWPORT_HEIGHT/);
  });

  it("sets inner container height to totalHeight", () => {
    expect(sourceCode).toMatch(/height:\s*totalHeight/);
  });

  it("uses translateY for offset positioning", () => {
    expect(sourceCode).toMatch(/translateY\s*\(\s*\$\{offsetY\}px\s*\)/);
  });

  it("listens to onScroll events to update scrollTop", () => {
    expect(sourceCode).toMatch(/onScroll=\{[\s\S]*?setScrollTop\s*\(\s*e\.currentTarget\.scrollTop\s*\)/);
  });

  it("has overflow-y-auto on scroll container", () => {
    expect(sourceCode).toMatch(/overflow-y-auto/);
  });

  it("uses position relative on inner container", () => {
    expect(sourceCode).toMatch(/position:\s*['"]relative['"]/);
  });
});

// ---------------------------------------------------------------------------
// 25. Loading and error states
// ---------------------------------------------------------------------------

describe("loading and error states", () => {
  it("shows loading message while loading project", () => {
    expect(sourceCode).toMatch(/Loading project/);
  });

  it("shows error message when project fails to load", () => {
    expect(sourceCode).toMatch(/Error loading project/);
  });

  it("shows loading timestamps message", () => {
    expect(sourceCode).toMatch(/Loading timestamps/);
  });

  it("conditionally renders loading timestamps text", () => {
    expect(sourceCode).toMatch(/loadingTimestamps\s*\?/);
  });
});

// ---------------------------------------------------------------------------
// 26. Continue / Advance button (Req 1 — onAdvance)
// ---------------------------------------------------------------------------

describe("Continue button", () => {
  it("renders Continue button text", () => {
    expect(sourceCode).toMatch(/Continue/);
  });

  it("button calls onAdvance on click", () => {
    expect(sourceCode).toMatch(/onClick=\{onAdvance\}/);
  });
});

// ---------------------------------------------------------------------------
// 27. Layout and structure
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// 28. Sticky table header
// ---------------------------------------------------------------------------

describe("Sticky table header", () => {
  it("thead row has sticky positioning", () => {
    expect(sourceCode).toMatch(/sticky top-0/);
  });

  it("sticky header has z-index", () => {
    expect(sourceCode).toMatch(/sticky top-0 z-10/);
  });
});

// ---------------------------------------------------------------------------
// 27. Layout and structure
// ---------------------------------------------------------------------------

describe("layout and structure", () => {
  it("uses space-y-6 for main layout spacing", () => {
    expect(sourceCode).toMatch(/space-y-6/);
  });

  it("uses rounded-lg border for section cards", () => {
    expect(sourceCode).toMatch(/rounded-lg\s+border/);
  });

  it("uses flex items-center justify-between for toolbar", () => {
    expect(sourceCode).toMatch(/flex\s+items-center\s+justify-between/);
  });

  it("uses flex justify-end for bottom button area", () => {
    expect(sourceCode).toMatch(/flex\s+justify-end/);
  });
});

// ---------------------------------------------------------------------------
// 29. Detect Segments button (Req 8)
// ---------------------------------------------------------------------------

describe("Detect Segments button", () => {
  it("renders Detect Segments button text", () => {
    expect(sourceCode).toMatch(/Detect Segments/);
  });

  it("defines handleDetectSegments as async function", () => {
    expect(sourceCode).toMatch(/const\s+handleDetectSegments\s*=\s*async/);
  });

  it("fetches GET /api/pipeline/tts-render/segments", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/tts-render\/segments['"]\s*\)/);
  });

  it("button calls handleDetectSegments on click", () => {
    expect(sourceCode).toMatch(/onClick=\{handleDetectSegments\}/);
  });

  it("button is disabled while detecting", () => {
    expect(sourceCode).toMatch(/disabled=\{detecting\}/);
  });

  it("shows Detecting… while loading", () => {
    expect(sourceCode).toMatch(/Detecting/);
  });

  it("tracks detecting state", () => {
    expect(sourceCode).toMatch(/\[\s*detecting\s*,\s*setDetecting\s*\]/);
  });

  it("tracks unmatchedSegments state", () => {
    expect(sourceCode).toMatch(/\[\s*unmatchedSegments\s*,\s*setUnmatchedSegments\s*\]/);
  });

  it("tracks overwriteExisting state", () => {
    expect(sourceCode).toMatch(/\[\s*overwriteExisting\s*,\s*setOverwriteExisting\s*\]/);
  });

  it("tracks autoFilledSections state", () => {
    expect(sourceCode).toMatch(/\[\s*autoFilledSections\s*,\s*setAutoFilledSections\s*\]/);
  });

  it("delegates detection to the shared audio-sync automation helper", () => {
    expect(sourceCode).toMatch(/fillMissingAudioSyncSectionGroups/);
  });

  it("renders Overwrite existing checkbox text", () => {
    expect(sourceCode).toMatch(/Overwrite existing/);
  });

  it("renders auto-detected badge text", () => {
    expect(sourceCode).toMatch(/\(auto-detected\)/);
  });
});

// ---------------------------------------------------------------------------
// 30. Unmatched segments warning (Req 8)
// ---------------------------------------------------------------------------

describe("unmatched segments warning", () => {
  it("shows 'did not match any section' text", () => {
    expect(sourceCode).toMatch(/did not match any section/);
  });

  it("references unmatchedSegments.length", () => {
    expect(sourceCode).toMatch(/unmatchedSegments\.length/);
  });
});

// ---------------------------------------------------------------------------
// 31. Save config SegmentRange conversion (Req 8)
// ---------------------------------------------------------------------------

describe("save config SegmentRange conversion", () => {
  it("imports the shared range conversion helper", () => {
    expect(sourceCode).toMatch(/toSegmentRangeSectionGroups/);
  });

  it("delegates range conversion to the shared helper", () => {
    expect(sourceCode).toMatch(/toSegmentRangeSectionGroups/);
  });
});

// ---------------------------------------------------------------------------
// 32. Detect Segments skips foreign-project segments (bug fix)
// ---------------------------------------------------------------------------

describe("Detect Segments skips foreign-project segments", () => {
  it("uses the shared helper that handles foreign-project segments", () => {
    expect(sourceCode).toMatch(/fillMissingAudioSyncSectionGroups/);
  });
});

// ---------------------------------------------------------------------------
// 33. Save Config preserves existing audioSync fields (bug fix)
// ---------------------------------------------------------------------------

describe("Save Config preserves existing audioSync fields", () => {
  it("spreads existing project audioSync into save payload", () => {
    expect(sourceCode).toMatch(/\.\.\.project\?\.audioSync/);
  });
});

// ---------------------------------------------------------------------------
// 34. Save Config error handling (bug fix)
// ---------------------------------------------------------------------------

describe("Save Config error handling", () => {
  it("checks response status after save", () => {
    expect(sourceCode).toMatch(/!res\.ok/);
  });
});

// ---------------------------------------------------------------------------
// 35. SegmentRange expansion on load (bug fix)
// ---------------------------------------------------------------------------

describe("SegmentRange expansion on load", () => {
  it("generates full segment range between start and end", () => {
    expect(sourceCode).toMatch(/normalizeAudioSyncSectionGroups/);
  });
});
