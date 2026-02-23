/**
 * Verification program for the AnnotationPanel component.
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

console.log('=== AnnotationPanel Module Verification ===\n');

// Import the module to verify exports
import * as AnnotationPanelModule from '../components/AnnotationPanel';

const defaultExport = AnnotationPanelModule.default;

console.log('Default export (AnnotationPanel):', typeof defaultExport === 'function' ? 'PASS (function)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'AnnotationPanel.tsx');
const source = fs.readFileSync(componentPath, 'utf-8');

// Requirement 9: 'use client' directive at the top
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 9 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props — annotations: Annotation[], sectionId: string, onBatchResolve: (jobId: string) => void
const hasAnnotationsProp = source.includes('annotations: Annotation[]');
const hasSectionIdProp = source.includes('sectionId: string');
const hasOnBatchResolveProp = source.includes('onBatchResolve: (jobId: string) => void');
console.log('Req 1 - Props (annotations: Annotation[]):', hasAnnotationsProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (sectionId: string):', hasSectionIdProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (onBatchResolve: (jobId: string) => void):', hasOnBatchResolveProp ? 'PASS' : 'FAIL');

// Requirement 2: Scrollable list sorted by timestamp ascending
const hasSortByTimestamp = source.includes('.sort((a, b) => a.timestamp - b.timestamp)');
const hasOverflowScroll = source.includes('overflow-y-auto');
console.log('Req 2 - Sorted by timestamp ascending:', hasSortByTimestamp ? 'PASS' : 'FAIL');
console.log('Req 2 - Scrollable list (overflow-y-auto):', hasOverflowScroll ? 'PASS' : 'FAIL');

// Requirement 3: Card shows timestamp (MM:SS.ms), thumbnail, text (truncated), severity badge, fix type badge, analysis summary
const hasFormatTs = source.includes('const formatTs');
const hasThumbnailImg = source.includes('className="w-20 h-11 object-cover rounded flex-shrink-0"');
const hasLineClamp2 = source.includes('line-clamp-2');
const hasLineClamp1 = source.includes('line-clamp-1');
console.log('Req 3 - Timestamp formatter (formatTs):', hasFormatTs ? 'PASS' : 'FAIL');
console.log('Req 3 - Thumbnail (80×45px = w-20 h-11):', hasThumbnailImg ? 'PASS' : 'FAIL');
console.log('Req 3 - Text truncated to 2 lines (line-clamp-2):', hasLineClamp2 ? 'PASS' : 'FAIL');
console.log('Req 3 - Analysis summary 1 line (line-clamp-1):', hasLineClamp1 ? 'PASS' : 'FAIL');

// Requirement 4: Cards expand on click, show technicalAssessment, suggestedFixes, Retry, Mark Resolved
const hasExpandToggle = source.includes('aria-expanded');
const hasTechnicalAssessment = source.includes('Technical assessment');
const hasSuggestedFixes = source.includes('Suggested fixes');
const hasRetryButton = source.includes('Retry');
const hasMarkResolvedButton = source.includes('Mark Resolved');
console.log('Req 4 - Cards expand on click (aria-expanded):', hasExpandToggle ? 'PASS' : 'FAIL');
console.log('Req 4 - Shows technicalAssessment:', hasTechnicalAssessment ? 'PASS' : 'FAIL');
console.log('Req 4 - Shows suggestedFixes list:', hasSuggestedFixes ? 'PASS' : 'FAIL');
console.log('Req 4 - Retry action:', hasRetryButton ? 'PASS' : 'FAIL');
console.log('Req 4 - Mark Resolved action:', hasMarkResolvedButton ? 'PASS' : 'FAIL');

// Requirement 5: [Apply N Fixes] button, POSTs to /api/sections/${sectionId}/resolve-batch, SseLogPanel
const hasApplyButton = source.includes('Apply ${unresolvedWithAnalysisCount} Fixes');
const hasBatchResolveUrl = source.includes('/api/sections/${sectionId}/resolve-batch');
const hasSseLogPanel = source.includes('<SseLogPanel');
const hasSseImport = source.includes("import { SseLogPanel }") || source.includes("import {SseLogPanel}");
console.log('Req 5 - [Apply N Fixes] button:', hasApplyButton ? 'PASS' : 'FAIL');
console.log('Req 5 - POST to /api/sections/${sectionId}/resolve-batch:', hasBatchResolveUrl ? 'PASS' : 'FAIL');
console.log('Req 5 - Uses SseLogPanel component:', hasSseLogPanel ? 'PASS' : 'FAIL');
console.log('Req 5 - Imports SseLogPanel:', hasSseImport ? 'PASS' : 'FAIL');

// Requirement 5 cont: N = count unresolved with non-null analysis
const hasUnresolvedCount = source.includes('!a.resolved') && source.includes('a.analysis !== null');
console.log('Req 5 - N = unresolved with non-null analysis:', hasUnresolvedCount ? 'PASS' : 'FAIL');

// Requirement 5 cont: onBatchResolve(data.jobId) called after POST
const callsOnBatchResolve = source.includes('onBatchResolve(data.jobId)');
console.log('Req 5 - Calls onBatchResolve(data.jobId):', callsOnBatchResolve ? 'PASS' : 'FAIL');

// Requirement 5 cont: disabled when N=0 or batch job in progress
const hasDisabledLogic = source.includes('unresolvedWithAnalysisCount === 0') && source.includes('batchJobId');
console.log('Req 5 - Button disabled when N=0 or batch in progress:', hasDisabledLogic ? 'PASS' : 'FAIL');

// Requirement 6: Resolving annotations (resolveJobId set) — inline progress spinner
const hasResolveJobId = source.includes('resolveJobId');
const hasSpinner = source.includes('Spinner') || source.includes('animate-spin');
console.log('Req 6 - Tracks resolveJobId for inline progress:', hasResolveJobId ? 'PASS' : 'FAIL');
console.log('Req 6 - Inline progress spinner:', hasSpinner ? 'PASS' : 'FAIL');

// Requirement 7: Resolved annotations — green "✓ Resolved" badge, collapsed by default
const hasResolvedBadge = source.includes('✓ Resolved');
const hasGreenResolvedStyling = source.includes('bg-green-500');
console.log('Req 7 - Green "✓ Resolved" badge:', hasResolvedBadge ? 'PASS' : 'FAIL');
console.log('Req 7 - Green styling (bg-green-500):', hasGreenResolvedStyling ? 'PASS' : 'FAIL');

// Requirement 8: Failed annotations — [Retry] button, POSTs to /api/jobs/${annotation.resolveJobId}/retry
const hasRetryPostUrl = source.includes('/api/jobs/${jobId}/retry');
const hasRetryPost = source.includes("method: 'POST'") && hasRetryPostUrl;
console.log('Req 8 - Retry POSTs to /api/jobs/${jobId}/retry:', hasRetryPost ? 'PASS' : 'FAIL');

// Requirement 10: Severity badge colors
const hasCriticalRed = source.includes("critical: 'bg-red-500'");
const hasMajorOrange = source.includes("major: 'bg-orange-500'");
const hasMinorYellow = source.includes("minor: 'bg-yellow-500'");
const hasPassGreen = source.includes("pass: 'bg-green-500'");
console.log('Req 10 - Severity critical=red:', hasCriticalRed ? 'PASS' : 'FAIL');
console.log('Req 10 - Severity major=orange:', hasMajorOrange ? 'PASS' : 'FAIL');
console.log('Req 10 - Severity minor=yellow:', hasMinorYellow ? 'PASS' : 'FAIL');
console.log('Req 10 - Severity pass=green:', hasPassGreen ? 'PASS' : 'FAIL');

// Instruction: Fix type labels
const hasRemotionLabel = source.includes("remotion: 'Remotion Fix'");
const hasVeoLabel = source.includes("veo: 'Veo Regen'");
const hasTtsLabel = source.includes("tts: 'TTS Re-render'");
const hasNoneLabel = source.includes("none: 'No Fix'");
console.log("Inst - Fix type label remotion='Remotion Fix':", hasRemotionLabel ? 'PASS' : 'FAIL');
console.log("Inst - Fix type label veo='Veo Regen':", hasVeoLabel ? 'PASS' : 'FAIL');
console.log("Inst - Fix type label tts='TTS Re-render':", hasTtsLabel ? 'PASS' : 'FAIL');
console.log("Inst - Fix type label none='No Fix':", hasNoneLabel ? 'PASS' : 'FAIL');

// Instruction: useState for expanded card state: Record<string, boolean>
const hasExpandedState = source.includes('useState<Record<string, boolean>>');
console.log('Inst - useState<Record<string, boolean>> for expanded:', hasExpandedState ? 'PASS' : 'FAIL');

// Instruction: formatTs helper matches spec
const hasFormatTsImpl = source.includes("const formatTs = (s: number)");
const hasFormatTsMath = source.includes('Math.floor(s / 60)') || source.includes('Math.floor(s/60)');
const hasFormatTsFixed = source.includes('toFixed(1)');
const hasFormatTsPad = source.includes("padStart(4, '0')") || source.includes('padStart(4,"0")');
console.log('Inst - formatTs helper defined:', hasFormatTsImpl ? 'PASS' : 'FAIL');
console.log('Inst - formatTs uses Math.floor for minutes:', hasFormatTsMath ? 'PASS' : 'FAIL');
console.log('Inst - formatTs uses toFixed(1):', hasFormatTsFixed ? 'PASS' : 'FAIL');
console.log("Inst - formatTs uses padStart(4, '0'):", hasFormatTsPad ? 'PASS' : 'FAIL');

// Import structure
const hasAnnotationTypeImport = source.includes('Annotation') && source.includes("from '../lib/types'");
const hasSseLogPanelImport = source.includes("from './SseLogPanel'");
console.log('Inst - Imports Annotation type from ../lib/types:', hasAnnotationTypeImport ? 'PASS' : 'FAIL');
console.log('Inst - Imports SseLogPanel from ./SseLogPanel:', hasSseLogPanelImport ? 'PASS' : 'FAIL');

// React hooks called only at top level (NOT inside .map())
// Check that useJob is NOT called inside the sorted.map callback
const mapCallbackRegex = /sorted\.map\(\s*\([\s\S]*?\)\s*=>\s*\{[\s\S]*?useJob[\s\S]*?\}\s*\)/;
const hookInMap = mapCallbackRegex.test(source);
console.log('Inst - useJob NOT called inside .map() (Rules of Hooks):', !hookInMap ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  typeof defaultExport === 'function',
  hasUseClient,
  hasAnnotationsProp, hasSectionIdProp, hasOnBatchResolveProp,
  hasSortByTimestamp, hasOverflowScroll,
  hasFormatTs, hasThumbnailImg, hasLineClamp2, hasLineClamp1,
  hasExpandToggle, hasTechnicalAssessment, hasSuggestedFixes, hasRetryButton, hasMarkResolvedButton,
  hasApplyButton, hasBatchResolveUrl, hasSseLogPanel, hasSseImport,
  hasUnresolvedCount, callsOnBatchResolve, hasDisabledLogic,
  hasResolveJobId, hasSpinner,
  hasResolvedBadge, hasGreenResolvedStyling,
  hasRetryPost,
  hasCriticalRed, hasMajorOrange, hasMinorYellow, hasPassGreen,
  hasRemotionLabel, hasVeoLabel, hasTtsLabel, hasNoneLabel,
  hasExpandedState,
  hasFormatTsImpl, hasFormatTsMath, hasFormatTsFixed, hasFormatTsPad,
  hasAnnotationTypeImport, hasSseLogPanelImport,
  !hookInMap,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nAnnotationPanel component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
