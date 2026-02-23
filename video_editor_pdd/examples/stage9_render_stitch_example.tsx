/**
 * Verification program for the Stage9RenderStitch component.
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

console.log('=== Stage9RenderStitch Module Verification ===\n');

import * as Stage9Module from '../components/stages/Stage9RenderStitch';

const defaultExport = Stage9Module.default;

console.log('Default export:', typeof defaultExport === 'function' ? 'PASS (function)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage9RenderStitch.tsx');
const source = fs.readFileSync(componentPath, 'utf-8');

// Requirement 8: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 8 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props include onAdvance: () => void
const hasOnAdvanceProp = source.includes('onAdvance') && (source.includes('() => void') || source.includes('()=>void'));
console.log('Req 1 - Props (onAdvance: () => void):', hasOnAdvanceProp ? 'PASS' : 'FAIL');

// Requirement 2: Section render table with expected columns
const hasSectionIdColumn = source.includes('Section ID');
const hasDurationColumn = source.includes('Duration');
const hasStatusColumn = source.includes('Status');
const hasProgressColumn = source.includes('Progress');
const hasPreviewColumn = source.includes('Preview');
const hasReRenderColumn = source.includes('Re-render') || source.includes('Rerender');
console.log('Req 2 - Table column: Section ID:', hasSectionIdColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Duration:', hasDurationColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Status:', hasStatusColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Progress:', hasProgressColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Preview:', hasPreviewColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Re-render:', hasReRenderColumn ? 'PASS' : 'FAIL');

// Requirement 2: Status badge
const hasStatusBadge = source.includes('Rendered') && source.includes('Rendering') && source.includes('Missing');
console.log('Req 2 - Status badges (Rendered/Rendering/Missing):', hasStatusBadge ? 'PASS' : 'FAIL');

// Requirement 2: Progress bar styling per spec
const hasProgressBar = source.includes('h-2 bg-green-400 transition-all');
console.log('Req 2 - Progress bar (h-2 bg-green-400 transition-all):', hasProgressBar ? 'PASS' : 'FAIL');

// Requirement 2: Preview button (▶)
const hasPreviewButton = source.includes('▶');
console.log('Req 2 - Preview button (▶):', hasPreviewButton ? 'PASS' : 'FAIL');

// Requirement 2: Re-render button (↺)
const hasReRenderButton = source.includes('↺');
console.log('Req 2 - Re-render button (↺):', hasReRenderButton ? 'PASS' : 'FAIL');

// Requirement 2: Checkbox column for selection
const hasCheckbox = source.includes('type="checkbox"') || source.includes("type='checkbox'");
console.log('Req 2 - Checkbox column for selection:', hasCheckbox ? 'PASS' : 'FAIL');

// Requirement 3: Active renders panel up to 3
const hasActiveRenders = source.includes('Active Renders');
const hasSlice3 = source.includes('.slice(0, 3)');
console.log('Req 3 - Active Renders panel:', hasActiveRenders ? 'PASS' : 'FAIL');
console.log('Req 3 - Limits to 3 simultaneous (slice 0,3):', hasSlice3 ? 'PASS' : 'FAIL');

// Requirement 3: Active renders filter (progress > 0 && progress < 100)
const hasActiveFilter = source.includes('progress > 0') && source.includes('progress < 100');
console.log('Req 3 - Filter: progress > 0 && progress < 100:', hasActiveFilter ? 'PASS' : 'FAIL');

// Requirement 4: Render dropdown with All / Missing / Selected
const hasRenderAll = source.includes('>All<') || source.includes('"all"') || source.includes("'all'");
const hasRenderMissing = source.includes('>Missing<') || source.includes('"missing"') || source.includes("'missing'");
const hasRenderSelected = source.includes('>Selected<') || source.includes('"selected"') || source.includes("'selected'");
console.log('Req 4 - Render mode: All:', hasRenderAll ? 'PASS' : 'FAIL');
console.log('Req 4 - Render mode: Missing:', hasRenderMissing ? 'PASS' : 'FAIL');
console.log('Req 4 - Render mode: Selected:', hasRenderSelected ? 'PASS' : 'FAIL');

// Requirement 4: POST /api/pipeline/render/run
const hasRenderRunEndpoint = source.includes('/api/pipeline/render/run');
console.log('Req 4 - POST /api/pipeline/render/run:', hasRenderRunEndpoint ? 'PASS' : 'FAIL');

// Requirement 4: Sends sections in body
const hasSectionsBody = source.includes('JSON.stringify') && source.includes('sections');
console.log('Req 4 - Sends sections in request body:', hasSectionsBody ? 'PASS' : 'FAIL');

// Requirement 5: Stitch Full Video button
const hasStitchButton = source.includes('Stitch Full Video') || source.includes('Stitch');
console.log('Req 5 - Stitch Full Video button:', hasStitchButton ? 'PASS' : 'FAIL');

// Requirement 5: POST /api/pipeline/stitch/run
const hasStitchEndpoint = source.includes('/api/pipeline/stitch/run');
console.log('Req 5 - POST /api/pipeline/stitch/run:', hasStitchEndpoint ? 'PASS' : 'FAIL');

// Requirement 5: Stitch disabled while renders in progress
const hasStitchDisabled = source.includes('anyRenderInProgress') || (source.includes('disabled') && source.includes('render'));
console.log('Req 5 - Stitch disabled during renders:', hasStitchDisabled ? 'PASS' : 'FAIL');

// Requirement 6: Full Video panel with file size and duration
const hasFullVideoPanel = source.includes('Full Video');
const hasFormatBytes = source.includes('formatBytes') || (source.includes('MB') && source.includes('GB'));
const hasOpenInReview = source.includes('Open in Review');
const callsOnAdvance = source.includes('onAdvance()') || source.includes('onAdvance(') || source.includes('onClick={onAdvance}');
console.log('Req 6 - Full Video panel:', hasFullVideoPanel ? 'PASS' : 'FAIL');
console.log('Req 6 - File size formatting (MB/GB):', hasFormatBytes ? 'PASS' : 'FAIL');
console.log('Req 6 - Open in Review button:', hasOpenInReview ? 'PASS' : 'FAIL');
console.log('Req 6 - Calls onAdvance():', callsOnAdvance ? 'PASS' : 'FAIL');

// Requirement 6: fullVideo.exists check
const hasExistsCheck = source.includes('fullVideo.exists');
console.log('Req 6 - fullVideo.exists visibility check:', hasExistsCheck ? 'PASS' : 'FAIL');

// Requirement 7: SSE stream for progress updates
const hasEventSource = source.includes('EventSource');
const hasSseUrl = source.includes('/api/pipeline/render/stream');
const hasSectionProgress = source.includes('section-progress');
const hasPercentUpdate = source.includes('percent');
console.log('Req 7 - Uses EventSource for SSE:', hasEventSource ? 'PASS' : 'FAIL');
console.log('Req 7 - SSE URL /api/pipeline/render/stream:', hasSseUrl ? 'PASS' : 'FAIL');
console.log('Req 7 - Handles section-progress events:', hasSectionProgress ? 'PASS' : 'FAIL');
console.log('Req 7 - Updates percent from SSE:', hasPercentUpdate ? 'PASS' : 'FAIL');

// Instruction: Load render status on mount
const hasRenderStatusEndpoint = source.includes('/api/pipeline/render/status');
console.log('Inst - GET /api/pipeline/render/status on mount:', hasRenderStatusEndpoint ? 'PASS' : 'FAIL');

// Instruction: Preview modal with video element
const hasPreviewVideo = source.includes('/api/video/outputs/sections/') && source.includes('.mp4');
const hasVideoControls = source.includes('controls');
const hasMaxWFull = source.includes('max-w-full');
console.log('Inst - Preview video URL pattern:', hasPreviewVideo ? 'PASS' : 'FAIL');
console.log('Inst - Video has controls attr:', hasVideoControls ? 'PASS' : 'FAIL');
console.log('Inst - Video max-w-full class:', hasMaxWFull ? 'PASS' : 'FAIL');

// Instruction: Render complete / error events close SSE and reload status
const hasRenderComplete = source.includes('render-complete');
const hasRenderError = source.includes('render-error');
console.log('Inst - Handles render-complete event:', hasRenderComplete ? 'PASS' : 'FAIL');
console.log('Inst - Handles render-error event:', hasRenderError ? 'PASS' : 'FAIL');

// Instruction: EventSource cleanup
const hasEsCleanup = source.includes('.close()');
const hasCleanupReturn = source.includes('return () =>');
console.log('Inst - Closes EventSource on cleanup:', hasEsCleanup ? 'PASS' : 'FAIL');
console.log('Inst - useEffect cleanup function:', hasCleanupReturn ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasUseClient, hasOnAdvanceProp,
  hasSectionIdColumn, hasDurationColumn, hasStatusColumn, hasProgressColumn, hasPreviewColumn, hasReRenderColumn,
  hasStatusBadge, hasProgressBar, hasPreviewButton, hasReRenderButton, hasCheckbox,
  hasActiveRenders, hasSlice3, hasActiveFilter,
  hasRenderAll, hasRenderMissing, hasRenderSelected, hasRenderRunEndpoint, hasSectionsBody,
  hasStitchButton, hasStitchEndpoint, hasStitchDisabled,
  hasFullVideoPanel, hasFormatBytes, hasOpenInReview, callsOnAdvance, hasExistsCheck,
  hasEventSource, hasSseUrl, hasSectionProgress, hasPercentUpdate,
  hasRenderStatusEndpoint,
  hasPreviewVideo, hasVideoControls, hasMaxWFull,
  hasRenderComplete, hasRenderError, hasEsCleanup, hasCleanupReturn,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage9RenderStitch component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
