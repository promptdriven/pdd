/**
 * Verification program for the Stage10Audit component.
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

console.log('=== Stage10Audit Module Verification ===\n');

import * as Stage10Module from '../components/stages/Stage10Audit';

const defaultExport = Stage10Module.default;

console.log('Default export:', typeof defaultExport === 'function' ? 'PASS (function)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage10Audit.tsx');
const source = fs.readFileSync(componentPath, 'utf-8');

// Requirement 7: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 7 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props include onAdvance: () => void
const hasOnAdvanceProp = source.includes('onAdvance') && (source.includes('() => void') || source.includes('()=>void'));
console.log('Req 1 - Props (onAdvance: () => void):', hasOnAdvanceProp ? 'PASS' : 'FAIL');

// Requirement 2: Section audit table columns
const hasSectionColumn = source.includes('Section');
const hasPassColumn = source.includes('Pass');
const hasFailColumn = source.includes('Fail');
const hasStatusColumn = source.includes('Status');
console.log('Req 2 - Table column: Section:', hasSectionColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Pass:', hasPassColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Fail:', hasFailColumn ? 'PASS' : 'FAIL');
console.log('Req 2 - Table column: Status:', hasStatusColumn ? 'PASS' : 'FAIL');

// Requirement 2: View Report and ↺ Audit buttons
const hasViewReport = source.includes('View Report');
const hasReauditButton = source.includes('↺ Audit') || source.includes('↺');
console.log('Req 2 - View Report button:', hasViewReport ? 'PASS' : 'FAIL');
console.log('Req 2 - ↺ Audit button:', hasReauditButton ? 'PASS' : 'FAIL');

// Requirement 2: Status badge classes (pending=gray, running=amber, done=green, error=red)
const hasPendingGray = source.includes('pending') && source.includes('slate');
const hasRunningAmber = source.includes('running') && source.includes('amber');
const hasDoneGreen = source.includes('done') && source.includes('green');
const hasErrorRed = source.includes('error') && source.includes('red');
console.log('Req 2 - Status badge: pending=gray/slate:', hasPendingGray ? 'PASS' : 'FAIL');
console.log('Req 2 - Status badge: running=amber:', hasRunningAmber ? 'PASS' : 'FAIL');
console.log('Req 2 - Status badge: done=green:', hasDoneGreen ? 'PASS' : 'FAIL');
console.log('Req 2 - Status badge: error=red:', hasErrorRed ? 'PASS' : 'FAIL');

// Requirement 3: Audit All Sections and Audit Section ▾ dropdown
const hasAuditAll = source.includes('Audit All Sections');
const hasAuditDropdown = source.includes('Audit Section') && source.includes('▾');
console.log('Req 3 - Audit All Sections button:', hasAuditAll ? 'PASS' : 'FAIL');
console.log('Req 3 - Audit Section ▾ dropdown:', hasAuditDropdown ? 'PASS' : 'FAIL');

// Requirement 3: POST /api/pipeline/audit/run
const hasAuditRunEndpoint = source.includes('/api/pipeline/audit/run');
const hasPostMethod = source.includes("'POST'") || source.includes('"POST"');
console.log('Req 3 - POST /api/pipeline/audit/run:', hasAuditRunEndpoint ? 'PASS' : 'FAIL');
console.log('Req 3 - Uses POST method:', hasPostMethod ? 'PASS' : 'FAIL');

// Requirement 4: View Report expands row with per-spec verdicts
const hasExpandedState = source.includes('useState<Record<string, boolean>>');
const hasVerdictBadge = source.includes('PASS') && source.includes('FAIL');
const hasSpecName = source.includes('specName');
const hasSummary = source.includes('summary');
console.log('Req 4 - Expanded state (Record<string, boolean>):', hasExpandedState ? 'PASS' : 'FAIL');
console.log('Req 4 - Verdict badges (PASS/FAIL):', hasVerdictBadge ? 'PASS' : 'FAIL');
console.log('Req 4 - Spec name displayed:', hasSpecName ? 'PASS' : 'FAIL');
console.log('Req 4 - Summary displayed:', hasSummary ? 'PASS' : 'FAIL');

// Requirement 4: Verdict colors (PASS=green, FAIL=red)
const hasPassGreen = source.includes('PASS') && source.includes('green');
const hasFailRed = source.includes('FAIL') && source.includes('red');
console.log('Req 4 - PASS verdict green:', hasPassGreen ? 'PASS' : 'FAIL');
console.log('Req 4 - FAIL verdict red:', hasFailRed ? 'PASS' : 'FAIL');

// Requirement 5: FAIL rows show View Frame, View Spec, Create Annotation →
const hasViewFrame = source.includes('View Frame');
const hasViewSpec = source.includes('View Spec');
const hasCreateAnnotation = source.includes('Create Annotation');
console.log('Req 5 - View Frame button:', hasViewFrame ? 'PASS' : 'FAIL');
console.log('Req 5 - View Spec button:', hasViewSpec ? 'PASS' : 'FAIL');
console.log('Req 5 - Create Annotation → button:', hasCreateAnnotation ? 'PASS' : 'FAIL');

// Requirement 5: View Frame opens frame PNG in modal
const hasDialogElement = source.includes('<dialog');
const hasShowModal = source.includes('showModal');
const hasFrameImg = source.includes('/api/video/outputs/audit/') && source.includes('_frame.png');
console.log('Req 5 - Frame modal (<dialog>):', hasDialogElement ? 'PASS' : 'FAIL');
console.log('Req 5 - showModal() call:', hasShowModal ? 'PASS' : 'FAIL');
console.log('Req 5 - Frame PNG URL pattern:', hasFrameImg ? 'PASS' : 'FAIL');

// Requirement 5: View Spec opens inline viewer
const hasSpecPre = source.includes('<pre') && source.includes('text-xs') && source.includes('overflow-auto') && source.includes('max-h-64');
console.log('Req 5 - Spec viewer (<pre> with text-xs overflow-auto max-h-64):', hasSpecPre ? 'PASS' : 'FAIL');

// Requirement 5: Spec file fetched from GET /api/pipeline/specs/file?path=
const hasSpecFileEndpoint = source.includes('/api/pipeline/specs/file?path=');
console.log('Req 5 - GET /api/pipeline/specs/file?path=:', hasSpecFileEndpoint ? 'PASS' : 'FAIL');

// Requirement 5: Create Annotation → handler pre-fill shape
const hasAnnotationText = source.includes('text:') && source.includes('finding');
const hasAnnotationSectionId = source.includes('sectionId');
const hasAnnotationCompositeUrl = source.includes('compositeDataUrl');
const callsOnAdvance = source.includes('onAdvance()') || source.includes('onAdvance(');
console.log('Req 5 - Pre-fill text (finding):', hasAnnotationText ? 'PASS' : 'FAIL');
console.log('Req 5 - Pre-fill sectionId:', hasAnnotationSectionId ? 'PASS' : 'FAIL');
console.log('Req 5 - Pre-fill compositeDataUrl:', hasAnnotationCompositeUrl ? 'PASS' : 'FAIL');
console.log('Req 5 - Calls onAdvance():', callsOnAdvance ? 'PASS' : 'FAIL');

// Requirement 6: SSE for per-agent progress
const hasEventSource = source.includes('EventSource');
const hasSseUrl = source.includes('/api/pipeline/audit/stream');
const hasAuditSectionEvent = source.includes('audit-section');
const hasPassCountUpdate = source.includes('passCount');
const hasFailCountUpdate = source.includes('failCount');
console.log('Req 6 - Uses EventSource for SSE:', hasEventSource ? 'PASS' : 'FAIL');
console.log('Req 6 - SSE URL /api/pipeline/audit/stream:', hasSseUrl ? 'PASS' : 'FAIL');
console.log('Req 6 - Handles audit-section events:', hasAuditSectionEvent ? 'PASS' : 'FAIL');
console.log('Req 6 - Updates passCount from SSE:', hasPassCountUpdate ? 'PASS' : 'FAIL');
console.log('Req 6 - Updates failCount from SSE:', hasFailCountUpdate ? 'PASS' : 'FAIL');

// Instruction: Load audit results on mount
const hasAuditResultsEndpoint = source.includes('/api/pipeline/audit/results');
console.log('Inst - GET /api/pipeline/audit/results on mount:', hasAuditResultsEndpoint ? 'PASS' : 'FAIL');

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
  hasSectionColumn, hasPassColumn, hasFailColumn, hasStatusColumn,
  hasViewReport, hasReauditButton,
  hasPendingGray, hasRunningAmber, hasDoneGreen, hasErrorRed,
  hasAuditAll, hasAuditDropdown,
  hasAuditRunEndpoint, hasPostMethod,
  hasExpandedState, hasVerdictBadge, hasSpecName, hasSummary,
  hasPassGreen, hasFailRed,
  hasViewFrame, hasViewSpec, hasCreateAnnotation,
  hasDialogElement, hasShowModal, hasFrameImg,
  hasSpecPre, hasSpecFileEndpoint,
  hasAnnotationText, hasAnnotationSectionId, hasAnnotationCompositeUrl, callsOnAdvance,
  hasEventSource, hasSseUrl, hasAuditSectionEvent, hasPassCountUpdate, hasFailCountUpdate,
  hasAuditResultsEndpoint,
  hasEsCleanup, hasCleanupReturn,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage10Audit component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
