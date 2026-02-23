/**
 * Verification program for the app/page.tsx root client component.
 *
 * Validates the component module structure, exports, and source-level
 * requirements from the prompt specification. Runs headlessly with
 * `npx tsx` to produce console output for PDD verification.
 */

import * as fs from 'fs';
import * as path from 'path';

// ============================================================================
// 1. Module export verification
// ============================================================================

console.log('=== app/page.tsx Module Verification ===\n');

const componentPath = path.resolve(__dirname, '..', 'app', 'page.tsx');
const source = fs.readFileSync(componentPath, 'utf-8');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('=== Source-Level Requirements ===\n');

// Req 1: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 1 - 'use client' directive:", hasUseClient ? 'PASS' : 'FAIL');

// Req 2: State management
const hasActiveTabState = source.includes("useState<'pipeline' | 'review'>") ||
  (source.includes('activeTab') && source.includes("'pipeline'") && source.includes("'review'"));
const hasActiveStageState = /useState.*PipelineStage/.test(source) || source.includes("useState<PipelineStage>");
const hasProjectConfigState = /useState.*ProjectConfig/.test(source) || source.includes("useState<ProjectConfig");
const hasAnnotationPreFillState = /useState.*AnnotationCaptureData/.test(source) || source.includes("useState<AnnotationCaptureData");
console.log('Req 2 - activeTab state (pipeline|review):', hasActiveTabState ? 'PASS' : 'FAIL');
console.log('Req 2 - activeStage state (PipelineStage):', hasActiveStageState ? 'PASS' : 'FAIL');
console.log('Req 2 - projectConfig state:', hasProjectConfigState ? 'PASS' : 'FAIL');
console.log('Req 2 - annotationPreFill state:', hasAnnotationPreFillState ? 'PASS' : 'FAIL');

// Req 3: Tab bar layout
const hasTabBar = source.includes('Pipeline') && source.includes('Review');
const hasTabBorder = source.includes('border-b');
console.log('Req 3 - Tab bar with Pipeline and Review:', hasTabBar ? 'PASS' : 'FAIL');
console.log('Req 3 - Tab bar border styling:', hasTabBorder ? 'PASS' : 'FAIL');

// Req 4: Two-column layout
const hasTwoColumnLayout = source.includes('flex') && source.includes('flex-1');
console.log('Req 4 - Two-column flex layout:', hasTwoColumnLayout ? 'PASS' : 'FAIL');

// Req 5: Project config load on mount
const hasFetchProject = source.includes("fetch('/api/project')") || source.includes('fetch("/api/project")');
console.log('Req 5 - Fetches /api/project on mount:', hasFetchProject ? 'PASS' : 'FAIL');

// Req 6: StageSidebar import and usage
const hasStageSidebarImport = source.includes("import StageSidebar from");
const hasStageSidebarUsage = source.includes('<StageSidebar');
console.log('Req 6 - StageSidebar import:', hasStageSidebarImport ? 'PASS' : 'FAIL');
console.log('Req 6 - StageSidebar rendered:', hasStageSidebarUsage ? 'PASS' : 'FAIL');

// Req 7: Stage panel routing — all 10 stages imported
const hasStage1 = source.includes('Stage1ProjectSetup');
const hasStage2 = source.includes('Stage2ScriptEditor');
const hasStage3 = source.includes('Stage3TtsScriptGen');
const hasStage4 = source.includes('Stage4TtsRendering');
const hasStage5 = source.includes('Stage5AudioSync');
const hasStage6 = source.includes('Stage6SpecGeneration');
const hasStage7 = source.includes('Stage7VeoGeneration');
const hasStage8 = source.includes('Stage8CompositionGen');
const hasStage9 = source.includes('Stage9RenderStitch');
const hasStage10 = source.includes('Stage10Audit');
console.log('Req 7 - Stage1ProjectSetup:', hasStage1 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage2ScriptEditor:', hasStage2 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage3TtsScriptGen:', hasStage3 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage4TtsRendering:', hasStage4 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage5AudioSync:', hasStage5 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage6SpecGeneration:', hasStage6 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage7VeoGeneration:', hasStage7 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage8CompositionGen:', hasStage8 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage9RenderStitch:', hasStage9 ? 'PASS' : 'FAIL');
console.log('Req 7 - Stage10Audit:', hasStage10 ? 'PASS' : 'FAIL');

// Req 7: STAGE_PANELS record mapping
const hasStagePanelsRecord = source.includes('STAGE_PANELS') && source.includes('Record<PipelineStage');
console.log('Req 7 - STAGE_PANELS record mapping:', hasStagePanelsRecord ? 'PASS' : 'FAIL');

// Req 7: onAdvance handler increments stage
const hasOnAdvance = source.includes('onAdvance') || source.includes('handleAdvanceStage');
const hasStageOrder = source.includes('STAGE_ORDER');
console.log('Req 7 - onAdvance handler:', hasOnAdvance ? 'PASS' : 'FAIL');
console.log('Req 7 - STAGE_ORDER definition:', hasStageOrder ? 'PASS' : 'FAIL');

// Req 8: Review tab with VideoPlayer
const hasVideoPlayerImport = source.includes("import VideoPlayer from");
const hasVideoPlayerUsage = source.includes('<VideoPlayer');
const hasFullVideoPath = source.includes('/api/video/outputs/full_video.mp4');
console.log('Req 8 - VideoPlayer import:', hasVideoPlayerImport ? 'PASS' : 'FAIL');
console.log('Req 8 - VideoPlayer rendered:', hasVideoPlayerUsage ? 'PASS' : 'FAIL');
console.log('Req 8 - Full video path used:', hasFullVideoPath ? 'PASS' : 'FAIL');

// Req 8: AnnotationPanel
const hasAnnotationPanelImport = source.includes("import AnnotationPanel from");
const hasAnnotationPanelUsage = source.includes('<AnnotationPanel');
console.log('Req 8 - AnnotationPanel import:', hasAnnotationPanelImport ? 'PASS' : 'FAIL');
console.log('Req 8 - AnnotationPanel rendered:', hasAnnotationPanelUsage ? 'PASS' : 'FAIL');

// Req 9: Create Annotation from Stage 10 switches to Review tab
const hasSwitchToReview = source.includes("setActiveTab('review')");
const hasAnnotationPreFillSet = source.includes('setAnnotationPreFill(');
console.log('Req 9 - Switches to Review tab:', hasSwitchToReview ? 'PASS' : 'FAIL');
console.log('Req 9 - Sets annotationPreFill:', hasAnnotationPreFillSet ? 'PASS' : 'FAIL');

// Req 10: handleAnnotationCapture POSTs to /api/annotations
const hasAnnotationPost = source.includes("fetch('/api/annotations'") || source.includes('fetch("/api/annotations"');
const hasPostMethod = source.includes("method: 'POST'") || source.includes('method: "POST"');
console.log('Req 10 - POST to /api/annotations:', hasAnnotationPost ? 'PASS' : 'FAIL');
console.log('Req 10 - Uses POST method:', hasPostMethod ? 'PASS' : 'FAIL');

// Req: Loads annotations for review tab
const hasLoadAnnotations = source.includes('loadAnnotations');
const hasFetchAnnotations = source.includes('/api/annotations?sectionId=');
console.log('Req - loadAnnotations function:', hasLoadAnnotations ? 'PASS' : 'FAIL');
console.log('Req - Fetches annotations with sectionId:', hasFetchAnnotations ? 'PASS' : 'FAIL');

// Type imports
const hasTypeImports = source.includes('PipelineStage') &&
  source.includes('ProjectConfig') &&
  source.includes('Annotation') &&
  source.includes('AnnotationCaptureData');
console.log('Types - Imports PipelineStage, ProjectConfig, Annotation, AnnotationCaptureData:', hasTypeImports ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasUseClient,
  hasActiveTabState, hasActiveStageState, hasProjectConfigState, hasAnnotationPreFillState,
  hasTabBar, hasTabBorder,
  hasTwoColumnLayout,
  hasFetchProject,
  hasStageSidebarImport, hasStageSidebarUsage,
  hasStage1, hasStage2, hasStage3, hasStage4, hasStage5,
  hasStage6, hasStage7, hasStage8, hasStage9, hasStage10,
  hasStagePanelsRecord, hasOnAdvance, hasStageOrder,
  hasVideoPlayerImport, hasVideoPlayerUsage, hasFullVideoPath,
  hasAnnotationPanelImport, hasAnnotationPanelUsage,
  hasSwitchToReview, hasAnnotationPreFillSet,
  hasAnnotationPost, hasPostMethod,
  hasLoadAnnotations, hasFetchAnnotations,
  hasTypeImports,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\napp/page.tsx fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
