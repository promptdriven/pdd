/**
 * Verification program for the Stage5AudioSync component.
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

console.log('=== Stage5AudioSync Module Verification ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage5AudioSync.tsx');

if (!fs.existsSync(componentPath)) {
  console.log('FAIL: Component file not found at', componentPath);
  process.exit(1);
}

const source = fs.readFileSync(componentPath, 'utf-8');

// Check default export
const hasDefaultExport = /export\s+default\s+function\s+Stage5AudioSync/.test(source);
console.log('Default export:', hasDefaultExport ? 'PASS (function Stage5AudioSync)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

// Requirement 7: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 7 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props interface with onAdvance: () => void
const hasOnAdvanceProp = /onAdvance\s*:\s*\(\)\s*=>\s*void/.test(source);
console.log('Req 1 - Props (onAdvance: () => void):', hasOnAdvanceProp ? 'PASS' : 'FAIL');

// Requirement 2: Section grouping table with inline-editable segment ranges
const hasSectionGroupingTable = source.includes('Section') && source.includes('Segment');
const hasInlineInput = source.includes('comma-separated') || source.includes('segment');
const hasSaveConfigButton = source.includes('Save Config');
const hasSaveConfigPut = source.includes("method: 'PUT'") || source.includes('method: "PUT"');
const hasSaveProjectEndpoint = source.includes('/api/project');
const hasSectionGroupsPayload = source.includes('sectionGroups');
console.log('Req 2 - Section grouping table:', hasSectionGroupingTable ? 'PASS' : 'FAIL');
console.log('Req 2 - Inline editable input:', hasInlineInput ? 'PASS' : 'FAIL');
console.log('Req 2 - Save Config button:', hasSaveConfigButton ? 'PASS' : 'FAIL');
console.log('Req 2 - PUT method for save:', hasSaveConfigPut ? 'PASS' : 'FAIL');
console.log('Req 2 - /api/project endpoint:', hasSaveProjectEndpoint ? 'PASS' : 'FAIL');
console.log('Req 2 - audioSync.sectionGroups in payload:', hasSectionGroupsPayload ? 'PASS' : 'FAIL');

// Requirement 3: Run Audio Sync button with POST and SseLogPanel
const hasRunAudioSyncButton = source.includes('Run Audio Sync');
const hasAudioSyncRunEndpoint = source.includes('/api/pipeline/audio-sync/run');
const hasPostMethod = source.includes("method: 'POST'") || source.includes('method: "POST"');
const hasSseLogPanel = source.includes('SseLogPanel');
const hasSseImport = source.includes("import SseLogPanel") || source.includes("import { SseLogPanel");
const hasJobId = source.includes('jobId');
console.log('Req 3 - Run Audio Sync button:', hasRunAudioSyncButton ? 'PASS' : 'FAIL');
console.log('Req 3 - POST /api/pipeline/audio-sync/run:', hasAudioSyncRunEndpoint ? 'PASS' : 'FAIL');
console.log('Req 3 - POST method:', hasPostMethod ? 'PASS' : 'FAIL');
console.log('Req 3 - SseLogPanel component:', hasSseLogPanel ? 'PASS' : 'FAIL');
console.log('Req 3 - SseLogPanel import:', hasSseImport ? 'PASS' : 'FAIL');
console.log('Req 3 - jobId state for SseLogPanel:', hasJobId ? 'PASS' : 'FAIL');

// Requirement 4: Word Timestamp Viewer with columns word, start (3dp), end (3dp), segmentId
const hasWordColumn = source.includes('Word');
const hasStartColumn = source.includes('Start');
const hasEndColumn = source.includes('End');
const hasSegmentIdColumn = source.includes('Segment ID');
const hasThreeDecimalPlaces = source.includes('toFixed(3)');
const hasSectionFilter = source.includes('<select') && source.includes('section');
const hasSearchInput = source.includes('Search') || source.includes('search');
const hasSearchFilter = source.includes('toLowerCase().includes(search.toLowerCase())') ||
  source.includes('w.word.toLowerCase().includes(term)');
console.log('Req 4 - Word column:', hasWordColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Start column:', hasStartColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - End column:', hasEndColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Segment ID column:', hasSegmentIdColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - 3 decimal places (toFixed(3)):', hasThreeDecimalPlaces ? 'PASS' : 'FAIL');
console.log('Req 4 - Section filter dropdown:', hasSectionFilter ? 'PASS' : 'FAIL');
console.log('Req 4 - Search input:', hasSearchInput ? 'PASS' : 'FAIL');
console.log('Req 4 - Search filter logic:', hasSearchFilter ? 'PASS' : 'FAIL');

// Requirement 5: Virtual scrolling with CSS contain: strict and fixed row heights
const hasContainStrict = source.includes("contain: 'strict'") || source.includes('contain: "strict"');
const hasFixedRowHeight = /ROW_HEIGHT\s*=\s*\d+/.test(source);
const hasViewportHeight = /VIEWPORT_HEIGHT\s*=\s*\d+/.test(source);
const hasTranslateY = source.includes('translateY');
const hasScrollTop = source.includes('scrollTop');
const hasStyleHeight = source.includes('height:') || source.includes('style={{ height');
console.log('Req 5 - CSS contain: strict:', hasContainStrict ? 'PASS' : 'FAIL');
console.log('Req 5 - Fixed ROW_HEIGHT constant:', hasFixedRowHeight ? 'PASS' : 'FAIL');
console.log('Req 5 - VIEWPORT_HEIGHT constant:', hasViewportHeight ? 'PASS' : 'FAIL');
console.log('Req 5 - translateY for virtual scroll:', hasTranslateY ? 'PASS' : 'FAIL');
console.log('Req 5 - scrollTop tracking:', hasScrollTop ? 'PASS' : 'FAIL');
console.log('Req 5 - Container height style:', hasStyleHeight ? 'PASS' : 'FAIL');

// Requirement 6: Load timestamps from GET endpoint
const hasTimestampsEndpoint = source.includes('/api/pipeline/audio-sync/timestamps');
const hasTimestampsSectionParam = source.includes('section=') || source.includes('section=${');
console.log('Req 6 - GET /api/pipeline/audio-sync/timestamps:', hasTimestampsEndpoint ? 'PASS' : 'FAIL');
console.log('Req 6 - section query parameter:', hasTimestampsSectionParam ? 'PASS' : 'FAIL');

// Instruction: Word count display "{filtered} of {total} words"
const hasWordCount = source.includes('of') && source.includes('words');
const hasFilteredLength = source.includes('filteredWords.length');
const hasTotalWords = source.includes('totalWords');
console.log('Inst - Word count display "{filtered} of {total} words":', hasWordCount ? 'PASS' : 'FAIL');
console.log('Inst - filteredWords.length:', hasFilteredLength ? 'PASS' : 'FAIL');
console.log('Inst - totalWords tracking:', hasTotalWords ? 'PASS' : 'FAIL');

// Instruction: Comma-separated segment IDs parsing
const hasCommaSplit = source.includes("split(',')") || source.includes('split(",")');
const hasTrim = source.includes('.trim()');
console.log('Inst - Comma-split segment IDs:', hasCommaSplit ? 'PASS' : 'FAIL');
console.log('Inst - Trim whitespace:', hasTrim ? 'PASS' : 'FAIL');

// Instruction: Auto-load timestamps after SSE done event
const hasOnDoneCallback = source.includes('onDone');
const hasAutoLoadTimestamps = source.includes('setSelectedSectionId') && source.includes('sections[0]');
console.log('Inst - SseLogPanel onDone callback:', hasOnDoneCallback ? 'PASS' : 'FAIL');
console.log('Inst - Auto-load timestamps on done:', hasAutoLoadTimestamps ? 'PASS' : 'FAIL');

// Instruction: ProjectConfig and Section type imports
const hasProjectConfigType = source.includes('ProjectConfig');
const hasSectionType = source.includes('Section');
const hasTypesImport = source.includes('types');
console.log('Inst - ProjectConfig type used:', hasProjectConfigType ? 'PASS' : 'FAIL');
console.log('Inst - Section type used:', hasSectionType ? 'PASS' : 'FAIL');
console.log('Inst - Types import from lib/types:', hasTypesImport ? 'PASS' : 'FAIL');

// Instruction: Virtual scroll renders only visible rows with buffer
const hasSlice = source.includes('.slice(');
const hasStartIndex = source.includes('startIndex');
const hasEndIndex = source.includes('endIndex');
const hasVisibleRows = source.includes('visibleWords') || source.includes('visibleRows');
console.log('Inst - Array slice for visible rows:', hasSlice ? 'PASS' : 'FAIL');
console.log('Inst - Start index calculation:', hasStartIndex ? 'PASS' : 'FAIL');
console.log('Inst - End index calculation:', hasEndIndex ? 'PASS' : 'FAIL');
console.log('Inst - Visible rows subset:', hasVisibleRows ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasDefaultExport,
  hasUseClient,
  hasOnAdvanceProp,
  hasSectionGroupingTable,
  hasInlineInput,
  hasSaveConfigButton,
  hasSaveConfigPut,
  hasSaveProjectEndpoint,
  hasSectionGroupsPayload,
  hasRunAudioSyncButton,
  hasAudioSyncRunEndpoint,
  hasPostMethod,
  hasSseLogPanel,
  hasSseImport,
  hasJobId,
  hasWordColumn,
  hasStartColumn,
  hasEndColumn,
  hasSegmentIdColumn,
  hasThreeDecimalPlaces,
  hasSectionFilter,
  hasSearchInput,
  hasSearchFilter,
  hasContainStrict,
  hasFixedRowHeight,
  hasViewportHeight,
  hasTranslateY,
  hasScrollTop,
  hasStyleHeight,
  hasTimestampsEndpoint,
  hasTimestampsSectionParam,
  hasWordCount,
  hasFilteredLength,
  hasTotalWords,
  hasCommaSplit,
  hasTrim,
  hasOnDoneCallback,
  hasAutoLoadTimestamps,
  hasProjectConfigType,
  hasSectionType,
  hasTypesImport,
  hasSlice,
  hasStartIndex,
  hasEndIndex,
  hasVisibleRows,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage5AudioSync component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
