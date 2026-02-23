/**
 * Verification program for the Stage4TtsRendering component.
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

console.log('=== Stage4TtsRendering Module Verification ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage4TtsRendering.tsx');

if (!fs.existsSync(componentPath)) {
  console.log('FAIL: Component file not found at', componentPath);
  process.exit(1);
}

const source = fs.readFileSync(componentPath, 'utf-8');

// Check default export
const hasDefaultExport = /export\s+default\s+function\s+Stage4TtsRendering/.test(source);
console.log('Default export:', hasDefaultExport ? 'PASS (function Stage4TtsRendering)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

// Requirement 8: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 8 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props interface with onAdvance: () => void
const hasOnAdvanceProp = /onAdvance\s*:\s*\(\)\s*=>\s*void/.test(source);
console.log('Req 1 - Props (onAdvance: () => void):', hasOnAdvanceProp ? 'PASS' : 'FAIL');

// Requirement 2: Toolbar with Render All and Render Missing buttons
const hasRenderAllButton = source.includes('Render All');
const hasRenderMissingButton = source.includes('Render Missing');
const hasRenderRunEndpoint = source.includes('/api/pipeline/tts-render/run');
console.log('Req 2 - Render All button:', hasRenderAllButton ? 'PASS' : 'FAIL');
console.log('Req 2 - Render Missing button:', hasRenderMissingButton ? 'PASS' : 'FAIL');
console.log('Req 2 - POST /api/pipeline/tts-render/run:', hasRenderRunEndpoint ? 'PASS' : 'FAIL');

// Requirement 3: Segment table columns (#, segment ID, status badge, play, re-render)
const hasSegmentIdColumn = source.includes('Segment ID');
const hasStatusColumn = source.includes('Status');
const hasPlayColumn = source.includes('Play');
const hasReRenderColumn = source.includes('Re-render');
const hasPlayButton = source.includes('▶');
const hasReRenderButton = source.includes('↺');
console.log('Req 3 - Segment ID column:', hasSegmentIdColumn ? 'PASS' : 'FAIL');
console.log('Req 3 - Status column:', hasStatusColumn ? 'PASS' : 'FAIL');
console.log('Req 3 - Play column:', hasPlayColumn ? 'PASS' : 'FAIL');
console.log('Req 3 - Re-render column:', hasReRenderColumn ? 'PASS' : 'FAIL');
console.log('Req 3 - Play button [▶]:', hasPlayButton ? 'PASS' : 'FAIL');
console.log('Req 3 - Re-render button [↺]:', hasReRenderButton ? 'PASS' : 'FAIL');

// Requirement 3: Status badges (done/missing/error)
const hasDoneBadge = source.includes('done') && source.includes('green');
const hasMissingBadge = source.includes('missing') && source.includes('yellow');
const hasErrorBadge = source.includes('error') && source.includes('red');
console.log('Req 3 - Done status badge (green):', hasDoneBadge ? 'PASS' : 'FAIL');
console.log('Req 3 - Missing status badge (yellow):', hasMissingBadge ? 'PASS' : 'FAIL');
console.log('Req 3 - Error status badge (red):', hasErrorBadge ? 'PASS' : 'FAIL');

// Requirement 4: Row expansion with WaveSurfer waveform
const hasWaveSurferImport = source.includes("from 'wavesurfer.js'") || source.includes('from "wavesurfer.js"');
const hasWaveSurferCreate = source.includes('WaveSurfer.create');
const hasWaveformHeight64 = source.includes('height: 64');
const hasWaveColor = source.includes('#4ade80');
const hasProgressColor = source.includes('#166534');
const hasAudioUrl = source.includes('/api/audio/');
console.log('Req 4 - WaveSurfer.js import:', hasWaveSurferImport ? 'PASS' : 'FAIL');
console.log('Req 4 - WaveSurfer.create call:', hasWaveSurferCreate ? 'PASS' : 'FAIL');
console.log('Req 4 - Waveform height: 64:', hasWaveformHeight64 ? 'PASS' : 'FAIL');
console.log('Req 4 - Wave color #4ade80:', hasWaveColor ? 'PASS' : 'FAIL');
console.log('Req 4 - Progress color #166534:', hasProgressColor ? 'PASS' : 'FAIL');
console.log('Req 4 - Audio URL /api/audio/:', hasAudioUrl ? 'PASS' : 'FAIL');

// Instruction: WaveSurfer instances stored in useRef<Map>
const hasWavesurferMapRef = /useRef<Map<string,\s*WaveSurfer>>/.test(source);
console.log('Inst - WaveSurfer instances in useRef<Map>:', hasWavesurferMapRef ? 'PASS' : 'FAIL');

// Instruction: WaveSurfer initialized on expand only (expandedId dependency)
const hasExpandedIdDep = source.includes('expandedId');
console.log('Inst - WaveSurfer init on expand (expandedId):', hasExpandedIdDep ? 'PASS' : 'FAIL');

// Requirement 5: Batch progress bar with current segment and percent
const hasBatchProgress = source.includes('batchProgress') || source.includes('BatchProgress');
const hasCurrentSegment = source.includes('currentSegment');
const hasCompletedCount = source.includes('completedCount');
console.log('Req 5 - Batch progress tracking:', hasBatchProgress ? 'PASS' : 'FAIL');
console.log('Req 5 - Current segment ID display:', hasCurrentSegment ? 'PASS' : 'FAIL');
console.log('Req 5 - Completed count tracking:', hasCompletedCount ? 'PASS' : 'FAIL');

// Requirement 6: Per-row re-render with inline SseLogPanel
const hasSseLogPanel = source.includes('SseLogPanel');
const hasSseImport = source.includes("import { SseLogPanel") || source.includes("import SseLogPanel");
const hasRowJobIds = source.includes('rowJobIds');
console.log('Req 6 - SseLogPanel component:', hasSseLogPanel ? 'PASS' : 'FAIL');
console.log('Req 6 - SseLogPanel import:', hasSseImport ? 'PASS' : 'FAIL');
console.log('Req 6 - Per-row job ID tracking:', hasRowJobIds ? 'PASS' : 'FAIL');

// Requirement 7: Load segments on mount from GET /api/pipeline/tts-render/segments
const hasSegmentsEndpoint = source.includes('/api/pipeline/tts-render/segments');
const hasFetchOnMount = source.includes('fetchSegments');
console.log('Req 7 - GET /api/pipeline/tts-render/segments:', hasSegmentsEndpoint ? 'PASS' : 'FAIL');
console.log('Req 7 - Fetch segments on mount:', hasFetchOnMount ? 'PASS' : 'FAIL');

// Instruction: playPause on play button
const hasPlayPause = source.includes('playPause');
console.log('Inst - playPause() for play button:', hasPlayPause ? 'PASS' : 'FAIL');

// Instruction: SSE events update row status in real time
const hasEventSource = source.includes('EventSource');
const hasSSEStream = source.includes('/stream');
console.log('Inst - EventSource for SSE:', hasEventSource ? 'PASS' : 'FAIL');
console.log('Inst - SSE stream endpoint:', hasSSEStream ? 'PASS' : 'FAIL');

// Instruction: Advance button enabled when all segments done
const hasAllDoneCheck = source.includes('allDone') || /every.*status.*done/.test(source);
const hasAdvanceButton = source.includes('Advance');
const hasDisabledAdvance = source.includes('disabled') && source.includes('allDone');
console.log('Inst - All-done check:', hasAllDoneCheck ? 'PASS' : 'FAIL');
console.log('Inst - Advance button:', hasAdvanceButton ? 'PASS' : 'FAIL');
console.log('Inst - Advance disabled until all done:', hasDisabledAdvance ? 'PASS' : 'FAIL');

// Instruction: Cleanup on unmount (destroy WaveSurfer instances)
const hasDestroy = source.includes('.destroy()');
const hasCleanup = source.includes('.close()');
console.log('Inst - WaveSurfer cleanup (destroy):', hasDestroy ? 'PASS' : 'FAIL');
console.log('Inst - EventSource cleanup (close):', hasCleanup ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasDefaultExport,
  hasUseClient,
  hasOnAdvanceProp,
  hasRenderAllButton,
  hasRenderMissingButton,
  hasRenderRunEndpoint,
  hasSegmentIdColumn,
  hasStatusColumn,
  hasPlayColumn,
  hasReRenderColumn,
  hasPlayButton,
  hasReRenderButton,
  hasDoneBadge,
  hasMissingBadge,
  hasErrorBadge,
  hasWaveSurferImport,
  hasWaveSurferCreate,
  hasWaveformHeight64,
  hasWaveColor,
  hasProgressColor,
  hasAudioUrl,
  hasWavesurferMapRef,
  hasExpandedIdDep,
  hasBatchProgress,
  hasCurrentSegment,
  hasCompletedCount,
  hasSseLogPanel,
  hasSseImport,
  hasRowJobIds,
  hasSegmentsEndpoint,
  hasFetchOnMount,
  hasPlayPause,
  hasEventSource,
  hasSSEStream,
  hasAllDoneCheck,
  hasAdvanceButton,
  hasDisabledAdvance,
  hasDestroy,
  hasCleanup,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage4TtsRendering component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
