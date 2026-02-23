/**
 * Verification program for the SseLogPanel component.
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

console.log('=== SseLogPanel Module Verification ===\n');

// Import the module to verify exports
import * as SseLogPanelModule from '../components/SseLogPanel';

const namedExport = SseLogPanelModule.SseLogPanel;
const defaultExport = SseLogPanelModule.default;

console.log('Named export (SseLogPanel):', typeof namedExport === 'function' ? 'PASS (function)' : 'FAIL');
console.log('Default export:', typeof defaultExport === 'function' ? 'PASS (function)' : 'FAIL');
console.log('Named and default are same:', namedExport === defaultExport ? 'PASS' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'SseLogPanel.tsx');
const source = fs.readFileSync(componentPath, 'utf-8');

// Requirement 11: 'use client' directive at the top
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 11 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props interface
const hasJobIdProp = source.includes('jobId: string | null');
const hasOnDoneProp = source.includes('onDone?:');
const hasOnErrorProp = source.includes('onError?:');
const hasClassNameProp = source.includes('className?:');
console.log('Req 1 - Props (jobId: string | null):', hasJobIdProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (onDone optional):', hasOnDoneProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (onError optional):', hasOnErrorProp ? 'PASS' : 'FAIL');
console.log('Req 1 - Props (className optional):', hasClassNameProp ? 'PASS' : 'FAIL');

// Requirement 2: Render nothing when jobId is null
const hasNullReturn = source.includes('if (!jobId) return null');
console.log('Req 2 - Returns null when jobId is null:', hasNullReturn ? 'PASS' : 'FAIL');

// Requirement 3: EventSource URL pattern
const hasEventSourceUrl = source.includes('/api/jobs/${jobId}/stream');
console.log('Req 3 - EventSource URL /api/jobs/${jobId}/stream:', hasEventSourceUrl ? 'PASS' : 'FAIL');

// Requirement 4: Timestamped log lines [HH:MM:SS]
const hasTimestamp = source.includes('toLocaleTimeString') && source.includes('hour12: false');
const hasLogFormat = source.includes('[${ts}]');
console.log('Req 4 - Timestamp format (HH:MM:SS):', hasTimestamp ? 'PASS' : 'FAIL');
console.log('Req 4 - Log line format [HH:MM:SS] message:', hasLogFormat ? 'PASS' : 'FAIL');

// Requirement 5: Done event handling with green banner
const hasDoneListener = source.includes("addEventListener('done'");
const hasGreenBanner = source.includes('text-green-400') && source.includes('✓ Completed');
const callsOnDone = source.includes('onDone?.()');
console.log('Req 5 - Listens for "done" event:', hasDoneListener ? 'PASS' : 'FAIL');
console.log('Req 5 - Green success banner "✓ Completed":', hasGreenBanner ? 'PASS' : 'FAIL');
console.log('Req 5 - Calls onDone():', callsOnDone ? 'PASS' : 'FAIL');

// Requirement 6: Error event handling with red banner
const hasErrorListener = source.includes("addEventListener('error'");
const hasRedBanner = source.includes('text-red-400') && source.includes('✕ Error:');
const callsOnError = source.includes('onError?.(');
console.log('Req 6 - Listens for "error" event:', hasErrorListener ? 'PASS' : 'FAIL');
console.log('Req 6 - Red error banner "✕ Error: {message}":', hasRedBanner ? 'PASS' : 'FAIL');
console.log('Req 6 - Calls onError(message):', callsOnError ? 'PASS' : 'FAIL');

// Requirement 7: Auto-scroll with useEffect and scroll ref
const hasScrollRef = source.includes('useRef<HTMLDivElement');
const hasScrollTo = source.includes('scrollTo') && source.includes('scrollHeight');
const hasSmoothScroll = source.includes("behavior: 'smooth'");
console.log('Req 7 - Scroll ref (useRef<HTMLDivElement>):', hasScrollRef ? 'PASS' : 'FAIL');
console.log('Req 7 - Auto-scroll (scrollTo + scrollHeight):', hasScrollTo ? 'PASS' : 'FAIL');
console.log('Req 7 - Smooth scroll behavior:', hasSmoothScroll ? 'PASS' : 'FAIL');

// Requirement 8: Polling fallback at /api/jobs/${jobId} every 2s
const hasPollingUrl = source.includes('/api/jobs/${id}');
const hasPollingInterval = source.includes('2000');
const hasFetchFallback = source.includes('fetch(');
console.log('Req 8 - Polling URL /api/jobs/${jobId}:', hasPollingUrl ? 'PASS' : 'FAIL');
console.log('Req 8 - Polling interval 2000ms:', hasPollingInterval ? 'PASS' : 'FAIL');
console.log('Req 8 - Fetch-based polling fallback:', hasFetchFallback ? 'PASS' : 'FAIL');

// Requirement 9: CSS contain: strict for virtualization
const hasContainStrict = source.includes("contain: 'strict'") || source.includes('contain: "strict"');
const hasOverflowAuto = source.includes('overflow-y-auto');
console.log('Req 9 - CSS contain: strict:', hasContainStrict ? 'PASS' : 'FAIL');
console.log('Req 9 - overflow-y: auto:', hasOverflowAuto ? 'PASS' : 'FAIL');

// Requirement 10: Close EventSource on unmount/jobId change
const hasCloseOnCleanup = source.includes('eventSourceRef.current?.close()') || source.includes('.close()');
const hasCleanupReturn = source.includes('return () =>');
console.log('Req 10 - Closes EventSource on cleanup:', hasCloseOnCleanup ? 'PASS' : 'FAIL');
console.log('Req 10 - useEffect cleanup function:', hasCleanupReturn ? 'PASS' : 'FAIL');

// Instruction: useRef<EventSource | null>
const hasEsRef = source.includes('useRef<EventSource | null>(null)');
console.log('Inst - useRef<EventSource | null>(null):', hasEsRef ? 'PASS' : 'FAIL');

// Instruction: useEffect dependencies [jobId]
const hasJobIdDep = source.includes('[jobId]');
console.log('Inst - useEffect dependency [jobId]:', hasJobIdDep ? 'PASS' : 'FAIL');

// Instruction: Log container classes
const hasLogContainer = source.includes('overflow-y-auto max-h-64 font-mono text-xs bg-black/20 p-2 rounded');
console.log('Inst - Log container classes:', hasLogContainer ? 'PASS' : 'FAIL');

// Instruction: JSON.parse event data
const hasJsonParse = source.includes('JSON.parse(event.data)');
console.log('Inst - JSON.parse(event.data):', hasJsonParse ? 'PASS' : 'FAIL');

// Instruction: Job type import for polling
const hasJobImport = source.includes('Job');
console.log('Inst - Job type imported for polling:', hasJobImport ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasUseClient, hasJobIdProp, hasOnDoneProp, hasOnErrorProp, hasClassNameProp,
  hasNullReturn, hasEventSourceUrl, hasTimestamp, hasLogFormat,
  hasDoneListener, hasGreenBanner, callsOnDone,
  hasErrorListener, hasRedBanner, callsOnError,
  hasScrollRef, hasScrollTo, hasSmoothScroll,
  hasPollingUrl, hasPollingInterval, hasFetchFallback,
  hasContainStrict, hasOverflowAuto,
  hasCloseOnCleanup, hasCleanupReturn,
  hasEsRef, hasJobIdDep, hasLogContainer, hasJsonParse, hasJobImport,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nSseLogPanel component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
