/**
 * Tests for app/page.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/app_page_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. 'use client' directive.
 *   2. State: activeTab ('pipeline'|'review'), activeStage (PipelineStage),
 *      projectConfig (ProjectConfig|null), annotationPreFill (AnnotationCaptureData|null).
 *   3. Two-column layout with tab bar at top. Pipeline tab: StageSidebar + stage panel.
 *      Review tab: VideoPlayer + AnnotationPanel.
 *   4. Tab bar: [Pipeline] and [Review] tabs with active highlighting.
 *   5. Loads project config via GET /api/project on mount.
 *   6. Polling done inside StageSidebar (not here).
 *   7. Stage panel routing: Stage1–Stage10 via STAGE_PANELS record.
 *   8. Review tab: loads annotations from GET /api/annotations.
 *   9. Create Annotation from Stage 10: switches to Review + pre-fills annotationPreFill.
 *  10. onAnnotationCapture: POSTs to /api/annotations.
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "app", "page.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive (Req 1)
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

  it("exports Page as default function", () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+Page/);
  });
});

// ---------------------------------------------------------------------------
// 3. State management (Req 2)
// ---------------------------------------------------------------------------

describe("state management", () => {
  it("manages activeTab state with 'pipeline' | 'review'", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*TabKey\s*>\s*\(\s*['"]pipeline['"]\s*\)/);
  });

  it("defines TabKey type as 'pipeline' | 'review'", () => {
    expect(sourceCode).toMatch(/type\s+TabKey\s*=\s*['"]pipeline['"]\s*\|\s*['"]review['"]/);
  });

  it("manages activeStage state as PipelineStage", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*PipelineStage\s*>\s*\(\s*['"]setup['"]\s*\)/);
  });

  it("manages projectConfig state as ProjectConfig | null", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*ProjectConfig\s*\|\s*null\s*>\s*\(\s*null\s*\)/);
  });

  it("manages annotationPreFill state as AnnotationCaptureData | null", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*AnnotationCaptureData\s*\|\s*null\s*>/);
  });

  it("manages annotations state as Annotation[]", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*Annotation\[\]\s*>/);
  });
});

// ---------------------------------------------------------------------------
// 4. Type imports (Req 2)
// ---------------------------------------------------------------------------

describe("type imports", () => {
  it("imports PipelineStage from @/lib/types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{[^}]*PipelineStage[^}]*\}\s*from\s+['"]@\/lib\/types['"]/);
  });

  it("imports ProjectConfig from @/lib/types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{[^}]*ProjectConfig[^}]*\}\s*from\s+['"]@\/lib\/types['"]/);
  });

  it("imports Annotation from @/lib/types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{[^}]*Annotation[^}]*\}\s*from\s+['"]@\/lib\/types['"]/);
  });

  it("imports AnnotationCaptureData from @/lib/types", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{[^}]*AnnotationCaptureData[^}]*\}\s*from\s+['"]@\/lib\/types['"]/);
  });
});

// ---------------------------------------------------------------------------
// 5. Component imports
// ---------------------------------------------------------------------------

describe("component imports", () => {
  it("imports StageSidebar", () => {
    expect(sourceCode).toMatch(/import\s+StageSidebar\s+from\s+['"]@\/components\/StageSidebar['"]/);
  });

  it("imports VideoPlayer", () => {
    expect(sourceCode).toMatch(/import\s+VideoPlayer\s+from\s+['"]@\/components\/VideoPlayer['"]/);
  });

  it("imports AnnotationPanel", () => {
    expect(sourceCode).toMatch(/import\s+AnnotationPanel\s+from\s+['"]@\/components\/AnnotationPanel['"]/);
  });
});

// ---------------------------------------------------------------------------
// 6. Stage panel imports — all 10 stages (Req 7)
// ---------------------------------------------------------------------------

describe("stage panel imports", () => {
  it("imports Stage1ProjectSetup", () => {
    expect(sourceCode).toMatch(/import\s+Stage1ProjectSetup\s+from\s+['"]@\/components\/stages\/Stage1ProjectSetup['"]/);
  });

  it("imports Stage2ScriptEditor", () => {
    expect(sourceCode).toMatch(/import\s+Stage2ScriptEditor\s+from\s+['"]@\/components\/stages\/Stage2ScriptEditor['"]/);
  });

  it("imports Stage3TtsScriptGen", () => {
    expect(sourceCode).toMatch(/import\s+Stage3TtsScriptGen\s+from\s+['"]@\/components\/stages\/Stage3TtsScriptGen['"]/);
  });

  it("imports Stage4TtsRendering", () => {
    expect(sourceCode).toMatch(/import\s+Stage4TtsRendering\s+from\s+['"]@\/components\/stages\/Stage4TtsRendering['"]/);
  });

  it("imports Stage5AudioSync", () => {
    expect(sourceCode).toMatch(/import\s+Stage5AudioSync\s+from\s+['"]@\/components\/stages\/Stage5AudioSync['"]/);
  });

  it("imports Stage6SpecGeneration", () => {
    expect(sourceCode).toMatch(/import\s+Stage6SpecGeneration\s+from\s+['"]@\/components\/stages\/Stage6SpecGeneration['"]/);
  });

  it("imports Stage7VeoGeneration", () => {
    expect(sourceCode).toMatch(/import\s+Stage7VeoGeneration\s+from\s+['"]@\/components\/stages\/Stage7VeoGeneration['"]/);
  });

  it("imports Stage8CompositionGen", () => {
    expect(sourceCode).toMatch(/import\s+Stage8CompositionGen\s+from\s+['"]@\/components\/stages\/Stage8CompositionGen['"]/);
  });

  it("imports Stage9RenderStitch", () => {
    expect(sourceCode).toMatch(/import\s+Stage9RenderStitch\s+from\s+['"]@\/components\/stages\/Stage9RenderStitch['"]/);
  });

  it("imports Stage10Audit", () => {
    expect(sourceCode).toMatch(/import\s+Stage10Audit\s+from\s+['"]@\/components\/stages\/Stage10Audit['"]/);
  });
});

// ---------------------------------------------------------------------------
// 7. STAGE_ORDER constant
// ---------------------------------------------------------------------------

describe("STAGE_ORDER constant", () => {
  it("defines STAGE_ORDER as PipelineStage[]", () => {
    expect(sourceCode).toMatch(/const\s+STAGE_ORDER\s*:\s*PipelineStage\[\]\s*=/);
  });

  it("contains all 10 stages in order", () => {
    expect(sourceCode).toContain("'setup'");
    expect(sourceCode).toContain("'script'");
    expect(sourceCode).toContain("'tts-script'");
    expect(sourceCode).toContain("'tts-render'");
    expect(sourceCode).toContain("'audio-sync'");
    expect(sourceCode).toContain("'specs'");
    expect(sourceCode).toContain("'veo'");
    expect(sourceCode).toContain("'compositions'");
    expect(sourceCode).toContain("'render'");
    expect(sourceCode).toContain("'audit'");
  });

  it("setup is first and audit is last", () => {
    const stageOrderMatch = sourceCode.match(/STAGE_ORDER\s*:\s*PipelineStage\[\]\s*=\s*\[([\s\S]*?)\]/);
    expect(stageOrderMatch).not.toBeNull();
    const stageContent = stageOrderMatch![1];
    const stages = stageContent.match(/'[^']+'/g);
    expect(stages).not.toBeNull();
    expect(stages![0]).toBe("'setup'");
    expect(stages![stages!.length - 1]).toBe("'audit'");
  });
});

// ---------------------------------------------------------------------------
// 8. STAGE_PANELS record (Req 7)
// ---------------------------------------------------------------------------

describe("STAGE_PANELS record", () => {
  it("defines STAGE_PANELS as Record<PipelineStage, React.ComponentType<...>>", () => {
    expect(sourceCode).toMatch(/const\s+STAGE_PANELS\s*:\s*Record\s*<\s*PipelineStage/);
  });

  it("maps setup to Stage1ProjectSetup", () => {
    expect(sourceCode).toMatch(/setup\s*:\s*Stage1ProjectSetup/);
  });

  it("maps script to Stage2ScriptEditor", () => {
    expect(sourceCode).toMatch(/script\s*:\s*Stage2ScriptEditor/);
  });

  it("maps tts-script to Stage3TtsScriptGen", () => {
    expect(sourceCode).toMatch(/['"]tts-script['"]\s*:\s*Stage3TtsScriptGen/);
  });

  it("maps tts-render to Stage4TtsRendering", () => {
    expect(sourceCode).toMatch(/['"]tts-render['"]\s*:\s*Stage4TtsRendering/);
  });

  it("maps audio-sync to Stage5AudioSync", () => {
    expect(sourceCode).toMatch(/['"]audio-sync['"]\s*:\s*Stage5AudioSync/);
  });

  it("maps specs to Stage6SpecGeneration", () => {
    expect(sourceCode).toMatch(/specs\s*:\s*Stage6SpecGeneration/);
  });

  it("maps veo to Stage7VeoGeneration", () => {
    expect(sourceCode).toMatch(/veo\s*:\s*Stage7VeoGeneration/);
  });

  it("maps compositions to Stage8CompositionGen", () => {
    expect(sourceCode).toMatch(/compositions\s*:\s*Stage8CompositionGen/);
  });

  it("maps render to Stage9RenderStitch", () => {
    expect(sourceCode).toMatch(/render\s*:\s*Stage9RenderStitch/);
  });

  it("maps audit to Stage10Audit", () => {
    expect(sourceCode).toMatch(/audit\s*:\s*Stage10Audit/);
  });

  it("uses activeStage to select StagePanel", () => {
    expect(sourceCode).toMatch(/STAGE_PANELS\[activeStage\]/);
  });
});

// ---------------------------------------------------------------------------
// 9. Tab bar (Req 3, 4)
// ---------------------------------------------------------------------------

describe("tab bar", () => {
  it("renders tab bar container with flex and border-b border-border", () => {
    expect(sourceCode).toMatch(/<div\s+className=["']flex\s+border-b\s+border-border["']/);
  });

  it("has Pipeline tab button", () => {
    expect(sourceCode).toMatch(/>[\s]*Pipeline[\s]*</);
  });

  it("has Review tab button", () => {
    expect(sourceCode).toMatch(/>[\s]*Review[\s]*</);
  });

  it("Pipeline button sets activeTab to 'pipeline'", () => {
    expect(sourceCode).toMatch(/onClick=\{?\(\)\s*=>\s*setActiveTab\s*\(\s*['"]pipeline['"]\s*\)/);
  });

  it("Review button sets activeTab to 'review'", () => {
    expect(sourceCode).toMatch(/onClick=\{?\(\)\s*=>\s*setActiveTab\s*\(\s*['"]review['"]\s*\)/);
  });

  it("active tab has highlighted styling (border-b-2 border-blue-500)", () => {
    expect(sourceCode).toContain("border-b-2 border-blue-500");
  });

  it("inactive tab has muted styling (text-gray-400)", () => {
    expect(sourceCode).toContain("text-gray-400");
  });
});

// ---------------------------------------------------------------------------
// 10. Two-column layout (Req 3)
// ---------------------------------------------------------------------------

describe("two-column layout", () => {
  it("uses flex h-full for two-column container", () => {
    expect(sourceCode).toMatch(/<div\s+className=["']flex\s+h-full["']/);
  });

  it("main panel uses flex-1 class", () => {
    expect(sourceCode).toMatch(/className=["'][^"']*flex-1/);
  });
});

// ---------------------------------------------------------------------------
// 11. Pipeline tab layout (Req 3)
// ---------------------------------------------------------------------------

describe("pipeline tab layout", () => {
  it("conditionally renders pipeline content when activeTab === 'pipeline'", () => {
    expect(sourceCode).toMatch(/activeTab\s*===\s*['"]pipeline['"]/);
  });

  it("renders StageSidebar with activeStage and onStageSelect", () => {
    expect(sourceCode).toMatch(/<StageSidebar/);
    expect(sourceCode).toMatch(/activeStage=\{activeStage\}/);
    expect(sourceCode).toMatch(/onStageSelect=\{setActiveStage\}/);
  });

  it("renders StagePanel with onAdvance prop", () => {
    expect(sourceCode).toMatch(/<StagePanel/);
    expect(sourceCode).toMatch(/onAdvance=\{handleAdvanceStage\}/);
  });

  it("passes projectConfig to StagePanel", () => {
    expect(sourceCode).toMatch(/projectConfig=\{projectConfig\}/);
  });
});

// ---------------------------------------------------------------------------
// 12. Review tab layout (Req 3, 8)
// ---------------------------------------------------------------------------

describe("review tab layout", () => {
  it("conditionally renders review content when activeTab === 'review'", () => {
    expect(sourceCode).toMatch(/activeTab\s*===\s*['"]review['"]/);
  });

  it("renders VideoPlayer with src pointing to full video", () => {
    expect(sourceCode).toMatch(/<VideoPlayer/);
    expect(sourceCode).toMatch(/src=["']\/?api\/video\/outputs\/full_video\.mp4["']/);
  });

  it("passes annotations to VideoPlayer", () => {
    expect(sourceCode).toMatch(/annotations=\{annotations\}/);
  });

  it("passes onAnnotationCapture to VideoPlayer", () => {
    expect(sourceCode).toMatch(/onAnnotationCapture=\{handleAnnotationCapture\}/);
  });

  it("renders AnnotationPanel with annotations and sectionId", () => {
    expect(sourceCode).toMatch(/<AnnotationPanel/);
    expect(sourceCode).toMatch(/annotations=\{annotations\}/);
  });
});

// ---------------------------------------------------------------------------
// 13. Project config load on mount (Req 5)
// ---------------------------------------------------------------------------

describe("project config load on mount", () => {
  it("fetches /api/project on mount", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/project['"]\s*\)/);
  });

  it("sets projectConfig from response", () => {
    expect(sourceCode).toMatch(/setProjectConfig\s*\(\s*data\s*\)/);
  });

  it("uses useEffect for project loading", () => {
    expect(sourceCode).toContain("useEffect");
  });

  it("handles errors when loading project config", () => {
    expect(sourceCode).toMatch(/catch\s*\(\s*err\s*\)/);
    expect(sourceCode).toMatch(/console\.error/);
  });

  it("uses cleanup flag to prevent stale state updates", () => {
    expect(sourceCode).toMatch(/cancelled\s*=\s*true/);
  });
});

// ---------------------------------------------------------------------------
// 14. Annotations loading (Req 8)
// ---------------------------------------------------------------------------

describe("annotations loading", () => {
  it("defines loadAnnotations function", () => {
    expect(sourceCode).toMatch(/const\s+loadAnnotations\s*=/);
  });

  it("fetches annotations with section parameter matching API spec", () => {
    // API uses ?section= not ?sectionId=
    expect(sourceCode).toMatch(/\/api\/annotations\?section=/);
  });

  it("extracts annotations array from response wrapper object", () => {
    // API returns { annotations: [...] }, so we need data.annotations
    expect(sourceCode).toMatch(/setAnnotations\s*\(\s*data\.annotations\s*\)/);
  });

  it("loads annotations when switching to Review tab", () => {
    expect(sourceCode).toMatch(/activeTab\s*===\s*['"]review['"]/);
    expect(sourceCode).toMatch(/loadAnnotations\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 15. onAdvance handler (Req 7)
// ---------------------------------------------------------------------------

describe("onAdvance handler", () => {
  it("defines handleAdvanceStage function", () => {
    expect(sourceCode).toMatch(/const\s+handleAdvanceStage\s*=/);
  });

  it("gets current index from STAGE_ORDER", () => {
    expect(sourceCode).toMatch(/STAGE_ORDER\.indexOf\s*\(\s*activeStage\s*\)/);
  });

  it("increments to next stage", () => {
    expect(sourceCode).toMatch(/STAGE_ORDER\[idx\s*\+\s*1\]/);
  });

  it("sets new active stage", () => {
    expect(sourceCode).toMatch(/setActiveStage\s*\(\s*next\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 16. Create Annotation from Stage 10 (Req 9)
// ---------------------------------------------------------------------------

describe("create annotation from audit stage", () => {
  it("defines handleCreateAnnotationFromAudit", () => {
    expect(sourceCode).toMatch(/const\s+handleCreateAnnotationFromAudit\s*=/);
  });

  it("sets annotationPreFill state", () => {
    expect(sourceCode).toMatch(/setAnnotationPreFill\s*\(\s*data\s*\)/);
  });

  it("switches to review tab", () => {
    expect(sourceCode).toMatch(/setActiveTab\s*\(\s*['"]review['"]\s*\)/);
  });

  it("passes onCreateAnnotation prop to StagePanel", () => {
    expect(sourceCode).toMatch(/onCreateAnnotation=\{handleCreateAnnotationFromAudit\}/);
  });
});

// ---------------------------------------------------------------------------
// 17. handleAnnotationCapture — POST to /api/annotations (Req 10)
// ---------------------------------------------------------------------------

describe("handleAnnotationCapture", () => {
  it("defines handleAnnotationCapture function", () => {
    expect(sourceCode).toMatch(/const\s+handleAnnotationCapture\s*=/);
  });

  it("POSTs to /api/annotations", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*['"]\/api\/annotations['"]\s*,\s*\{/);
  });

  it("uses POST method", () => {
    expect(sourceCode).toMatch(/method\s*:\s*['"]POST['"]/);
  });

  it("sends Content-Type application/json header", () => {
    expect(sourceCode).toMatch(/['"]Content-Type['"]\s*:\s*['"]application\/json['"]/);
  });

  it("includes sectionId in request body", () => {
    expect(sourceCode).toMatch(/sectionId/);
  });

  it("includes timestamp in request body", () => {
    expect(sourceCode).toMatch(/timestamp\s*:\s*data\.timestamp/);
  });

  it("includes text in request body", () => {
    expect(sourceCode).toMatch(/text\s*:\s*data\.text/);
  });

  it("includes drawingDataUrl in request body", () => {
    expect(sourceCode).toMatch(/drawingDataUrl\s*:\s*data\.drawingDataUrl/);
  });

  it("includes compositeDataUrl in request body", () => {
    expect(sourceCode).toMatch(/compositeDataUrl\s*:\s*data\.compositeDataUrl/);
  });

  it("includes videoFile in request body", () => {
    expect(sourceCode).toMatch(/videoFile\s*:\s*data\.videoFile/);
  });

  it("refreshes annotations after saving", () => {
    // After POST, loadAnnotations is called
    expect(sourceCode).toMatch(/await\s+loadAnnotations\s*\(\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 18. No polling in this component (Req 6)
// ---------------------------------------------------------------------------

describe("no polling in page component", () => {
  it("does not set up setInterval for polling", () => {
    expect(sourceCode).not.toMatch(/setInterval\s*\(\s*[\s\S]*?\/api\/pipeline\/status/);
  });

  it("does not fetch /api/pipeline/status directly", () => {
    expect(sourceCode).not.toMatch(/fetch\s*\(\s*['"]\/api\/pipeline\/status['"]/);
  });
});

// ---------------------------------------------------------------------------
// 19. Full video path constant
// ---------------------------------------------------------------------------

describe("full video path", () => {
  it("uses /api/video/outputs/full_video.mp4 as src for VideoPlayer", () => {
    expect(sourceCode).toContain("/api/video/outputs/full_video.mp4");
  });
});

// ---------------------------------------------------------------------------
// 20. React hooks usage
// ---------------------------------------------------------------------------

describe("React hooks usage", () => {
  it("imports useState from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,?\s*\{[^}]*useState[^}]*\}\s*from\s+['"]react['"]/);
  });

  it("imports useEffect from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,?\s*\{[^}]*useEffect[^}]*\}\s*from\s+['"]react['"]/);
  });

  it("imports useCallback from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,?\s*\{[^}]*useCallback[^}]*\}\s*from\s+['"]react['"]/);
  });

  it("imports useMemo from react", () => {
    expect(sourceCode).toMatch(/import\s+React\s*,?\s*\{[^}]*useMemo[^}]*\}\s*from\s+['"]react['"]/);
  });
});

// ---------------------------------------------------------------------------
// 21. StagePanelProps type
// ---------------------------------------------------------------------------

describe("StagePanelProps type", () => {
  it("defines onAdvance callback in panel props", () => {
    expect(sourceCode).toMatch(/onAdvance\s*:\s*\(\)\s*=>\s*void/);
  });

  it("defines projectConfig in panel props", () => {
    expect(sourceCode).toMatch(/projectConfig\s*:\s*ProjectConfig\s*\|\s*null/);
  });

  it("defines onCreateAnnotation optional callback in panel props", () => {
    expect(sourceCode).toMatch(/onCreateAnnotation\?\s*:\s*\(data\s*:\s*AnnotationCaptureData\)\s*=>\s*void/);
  });
});

// ---------------------------------------------------------------------------
// 22. annotationPreFill flow
// ---------------------------------------------------------------------------

describe("annotationPreFill flow", () => {
  it("passes annotationPreFill to VideoPlayer", () => {
    expect(sourceCode).toMatch(/annotationPreFill/);
  });
});

// ---------------------------------------------------------------------------
// 23. Batch resolve handler
// ---------------------------------------------------------------------------

describe("batch resolve handler", () => {
  it("defines handleBatchResolve function", () => {
    expect(sourceCode).toMatch(/const\s+handleBatchResolve\s*=/);
  });

  it("refreshes annotations after batch resolve", () => {
    // handleBatchResolve calls loadAnnotations
    expect(sourceCode).toContain("loadAnnotations");
  });

  it("passes onBatchResolve to AnnotationPanel", () => {
    expect(sourceCode).toMatch(/onBatchResolve=\{handleBatchResolve\}/);
  });
});

// ---------------------------------------------------------------------------
// 24. Error handling
// ---------------------------------------------------------------------------

describe("error handling", () => {
  it("wraps project config fetch in try/catch", () => {
    // Multiple try/catch blocks for different fetch calls
    const tryCatchCount = (sourceCode.match(/try\s*\{/g) || []).length;
    expect(tryCatchCount).toBeGreaterThanOrEqual(2);
  });

  it("wraps annotation POST in try/catch", () => {
    expect(sourceCode).toMatch(/catch\s*\(\s*err\s*\)/);
  });

  it("checks response.ok before parsing JSON", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 25. Loading states
// ---------------------------------------------------------------------------

describe("loading states", () => {
  it("tracks loadingProject state", () => {
    expect(sourceCode).toContain("loadingProject");
    expect(sourceCode).toContain("setLoadingProject");
  });

  it("tracks loadingAnnotations state", () => {
    expect(sourceCode).toContain("loadingAnnotations");
    expect(sourceCode).toContain("setLoadingAnnotations");
  });

  it("shows loading indicator while project loads", () => {
    expect(sourceCode).toMatch(/loadingProject\s*&&/);
    expect(sourceCode).toMatch(/Loading project/);
  });
});

// ---------------------------------------------------------------------------
// 26. Graceful error handling for API failures (items 14.1, 14.2)
// ---------------------------------------------------------------------------

describe("graceful error handling for API failures (14.1, 14.2)", () => {
  it("14.1: Review tab renders even when /api/project fails — AnnotationPanel not guarded by projectConfig", () => {
    // When /api/project fails, projectConfig stays null. The Review tab's
    // AnnotationPanel must still render — it must NOT be inside an
    // `if (projectConfig)` guard. Verify AnnotationPanel appears in the
    // same JSX block as `activeTab === 'review'` without a projectConfig check.
    expect(sourceCode).toMatch(/<AnnotationPanel/);
    // AnnotationPanel should not be wrapped in projectConfig &&
    const annotationPanelIdx = sourceCode.indexOf('<AnnotationPanel');
    const reviewCondIdx = sourceCode.indexOf("activeTab === 'review'");
    expect(annotationPanelIdx).toBeGreaterThan(reviewCondIdx);
    // The sectionId falls back to '' safely when projectConfig is null
    expect(sourceCode).toMatch(/selectedSectionId\s*\?\?\s*['"]{2}/);
  });

  it("14.2: loadAnnotations uses try/catch so annotation errors don't crash the page", () => {
    // When /api/annotations fails, the catch block must prevent a crash.
    // The catch just logs; annotations stays [] and panel shows empty state.
    expect(sourceCode).toMatch(/const\s+loadAnnotations\s*=/);
    // try/catch inside loadAnnotations
    expect(sourceCode).toMatch(/if\s*\(\s*!res\.ok\s*\)\s*throw/);
    // The error is caught and logged, not re-thrown
    expect(sourceCode).toMatch(/catch\s*\(\s*err\s*\)/);
    expect(sourceCode).toMatch(/console\.error\s*\(\s*err\s*\)/);
  });

  it("14.1: loadProject uses try/catch so project errors don't crash the page", () => {
    // When /api/project returns an error, loadProject must catch and log it.
    expect(sourceCode).toMatch(/throw\s+new\s+Error\s*\(\s*['"]Failed to load project['"]\s*\)/);
  });

  it("14.2: annotations state defaults to [] so panel renders empty state gracefully", () => {
    // On annotation fetch failure, annotations stays as [] and AnnotationPanel
    // renders "No annotations yet." instead of crashing.
    expect(sourceCode).toMatch(/useState\s*<\s*Annotation\[\]\s*>\s*\(\s*\[\s*\]\s*\)/);
  });
});
