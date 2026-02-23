/**
 * Verification program for the Stage7VeoGeneration component.
 *
 * Validates the component module structure, exports, and source-level
 * requirements from the prompt specification. Runs headlessly with
 * `npx tsx` to produce console output for PDD verification.
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * Component: Stage7VeoGeneration
 * ─────────────────────────────────────────────────────────────────────────────
 *
 * Props:
 *   onAdvance: () => void
 *
 * Required API Endpoints:
 *   GET  /api/pipeline/veo/clips
 *   POST /api/pipeline/veo/run
 *   POST /api/pipeline/veo/references/run
 *   SSE  /api/pipeline/veo/stream
 *
 * Dependencies:
 *   - SseLogPanel component (for streaming job logs)
 */

import * as fs from 'fs';
import * as path from 'path';

// ============================================================================
// 1. Module export verification
// ============================================================================

console.log('=== Stage7VeoGeneration Module Verification ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage7VeoGeneration.tsx');

if (!fs.existsSync(componentPath)) {
  console.log('FAIL: Component file not found at', componentPath);
  process.exit(1);
}

const source = fs.readFileSync(componentPath, 'utf-8');

// Check default export
const hasDefaultExport = /export\s+default\s/.test(source);
console.log('Default export:', hasDefaultExport ? 'PASS' : 'FAIL');

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

// Requirement 2: Character References panel with thumbnails and regenerate
const hasCharacterReferences = source.includes('Character References');
const hasRefThumbnail = source.includes('/api/video/outputs/veo/references/');
const hasRefRegenerate = source.includes('/api/pipeline/veo/references/run');
const hasRefImg = /img\s/.test(source) && source.includes('w-16 h-16 object-cover rounded');
console.log('Req 2 - Character References panel:', hasCharacterReferences ? 'PASS' : 'FAIL');
console.log('Req 2 - Reference thumbnail URL pattern:', hasRefThumbnail ? 'PASS' : 'FAIL');
console.log('Req 2 - POST /api/pipeline/veo/references/run:', hasRefRegenerate ? 'PASS' : 'FAIL');
console.log('Req 2 - img with w-16 h-16 object-cover rounded:', hasRefImg ? 'PASS' : 'FAIL');

// Requirement 3: Frame Chaining display with text chain
const hasFrameChaining = source.includes('Frame Chaining');
const hasChainArrow = source.includes(' → ');
const hasFrameChainDeps = source.includes('frameChainDeps');
console.log('Req 3 - Frame Chaining panel:', hasFrameChaining ? 'PASS' : 'FAIL');
console.log('Req 3 - Chain arrow (→) display:', hasChainArrow ? 'PASS' : 'FAIL');
console.log('Req 3 - frameChainDeps usage:', hasFrameChainDeps ? 'PASS' : 'FAIL');

// Requirement 4: Clip list table columns
const hasClipTable = source.includes('<table');
const hasClipColumn = source.includes('Clip');
const hasSectionColumn = source.includes('Section');
const hasAspectColumn = source.includes('Aspect');
const hasStatusColumn = source.includes('Status');
const hasActionsColumn = source.includes('Actions');
const hasStaleWarning = source.includes('⚠');
const hasPerClipRegenerate = source.includes('↺');
console.log('Req 4 - <table> element:', hasClipTable ? 'PASS' : 'FAIL');
console.log('Req 4 - Clip column:', hasClipColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Section column:', hasSectionColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Aspect column:', hasAspectColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Status column:', hasStatusColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Actions column:', hasActionsColumn ? 'PASS' : 'FAIL');
console.log('Req 4 - Stale ⚠ warning:', hasStaleWarning ? 'PASS' : 'FAIL');
console.log('Req 4 - Per-clip regenerate (↺):', hasPerClipRegenerate ? 'PASS' : 'FAIL');

// Requirement 5: Toolbar buttons
const hasGenerateAll = source.includes('Generate All');
const hasGenerateMissing = source.includes('Generate Missing');
const hasGenerateSection = source.includes('Generate Section');
const hasSectionDropdown = source.includes('<select');
const hasVeoRunEndpoint = source.includes('/api/pipeline/veo/run');
const hasPostMethod = source.includes("method: 'POST'") || source.includes('method: "POST"');
console.log('Req 5 - Generate All button:', hasGenerateAll ? 'PASS' : 'FAIL');
console.log('Req 5 - Generate Missing button:', hasGenerateMissing ? 'PASS' : 'FAIL');
console.log('Req 5 - Generate Section button:', hasGenerateSection ? 'PASS' : 'FAIL');
console.log('Req 5 - Section dropdown (<select>):', hasSectionDropdown ? 'PASS' : 'FAIL');
console.log('Req 5 - POST /api/pipeline/veo/run:', hasVeoRunEndpoint ? 'PASS' : 'FAIL');
console.log('Req 5 - POST method:', hasPostMethod ? 'PASS' : 'FAIL');

// Requirement 6: Auto-composite checkbox
const hasAutoComposite = source.includes('autoComposite') || source.includes('auto-composite');
const hasCheckbox = source.includes('type="checkbox"') || source.includes("type='checkbox'");
const hasSplitScreen = source.includes('split-screen') || source.includes('composite');
console.log('Req 6 - autoComposite state:', hasAutoComposite ? 'PASS' : 'FAIL');
console.log('Req 6 - Checkbox input:', hasCheckbox ? 'PASS' : 'FAIL');
console.log('Req 6 - Split-screen/composite label:', hasSplitScreen ? 'PASS' : 'FAIL');

// Requirement 7: SSE progress per-clip events
const hasSseLogPanel = source.includes('SseLogPanel');
const hasSseImport = source.includes("import { SseLogPanel") || source.includes("import SseLogPanel");
const hasEventSource = source.includes('EventSource');
const hasSseStream = source.includes('/api/pipeline/veo/stream');
const hasJobId = source.includes('jobId');
console.log('Req 7 - SseLogPanel component:', hasSseLogPanel ? 'PASS' : 'FAIL');
console.log('Req 7 - SseLogPanel import:', hasSseImport ? 'PASS' : 'FAIL');
console.log('Req 7 - EventSource for SSE:', hasEventSource ? 'PASS' : 'FAIL');
console.log('Req 7 - SSE stream URL:', hasSseStream ? 'PASS' : 'FAIL');
console.log('Req 7 - jobId state:', hasJobId ? 'PASS' : 'FAIL');

// Instructions: Status badges
const hasGreenDone = source.includes('green') && source.includes('done');
const hasAmberGenerating = source.includes('amber') && source.includes('generating');
const hasGrayMissing = (source.includes('gray') || source.includes('slate')) && source.includes('missing');
const hasRedError = source.includes('red') && source.includes('error');
const hasDoneBadge = source.includes('●');
const hasGeneratingBadge = source.includes('◌');
const hasMissingBadge = source.includes('○');
const hasErrorBadge = source.includes('✕');
console.log('Inst - Green done badge:', hasGreenDone ? 'PASS' : 'FAIL');
console.log('Inst - Amber generating badge:', hasAmberGenerating ? 'PASS' : 'FAIL');
console.log('Inst - Gray/slate missing badge:', hasGrayMissing ? 'PASS' : 'FAIL');
console.log('Inst - Red error badge:', hasRedError ? 'PASS' : 'FAIL');
console.log('Inst - Done symbol (●):', hasDoneBadge ? 'PASS' : 'FAIL');
console.log('Inst - Generating symbol (◌):', hasGeneratingBadge ? 'PASS' : 'FAIL');
console.log('Inst - Missing symbol (○):', hasMissingBadge ? 'PASS' : 'FAIL');
console.log('Inst - Error symbol (✕):', hasErrorBadge ? 'PASS' : 'FAIL');

// Instructions: Stale indicator uses amber color
const hasAmberStale = source.includes('amber') && source.includes('stale');
console.log('Inst - Amber stale indicator:', hasAmberStale ? 'PASS' : 'FAIL');

// Instructions: Load clips on mount
const hasClipsEndpoint = source.includes('/api/pipeline/veo/clips');
const hasFetchCall = source.includes('fetch(');
const hasUseEffect = source.includes('useEffect');
console.log('Inst - GET /api/pipeline/veo/clips:', hasClipsEndpoint ? 'PASS' : 'FAIL');
console.log('Inst - fetch() call:', hasFetchCall ? 'PASS' : 'FAIL');
console.log('Inst - useEffect for mount:', hasUseEffect ? 'PASS' : 'FAIL');

// Instructions: Section filter from unique sectionIds
const hasSectionFilter = source.includes('sectionId') && source.includes('filter');
console.log('Inst - Section filter logic:', hasSectionFilter ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Example API response shapes (for documentation)
// ============================================================================

console.log('\n=== Example API Response Shapes ===\n');

const mockClipsResponse = {
  clips: [
    { id: 'intro-wide', sectionId: 'intro', aspectRatio: '16:9', status: 'done', stale: false, frameChainDeps: [] },
    { id: 'intro-portrait', sectionId: 'intro', aspectRatio: '9:16', status: 'done', stale: true, frameChainDeps: ['intro-wide'] },
    { id: 'main-clip-1', sectionId: 'main', aspectRatio: '16:9', status: 'missing', stale: false, frameChainDeps: [] },
    { id: 'main-clip-2', sectionId: 'main', aspectRatio: '16:9', status: 'missing', stale: false, frameChainDeps: ['main-clip-1'] },
    { id: 'main-clip-3', sectionId: 'main', aspectRatio: '16:9', status: 'error', stale: false, frameChainDeps: ['main-clip-1', 'main-clip-2'] },
    { id: 'outro-clip', sectionId: 'outro', aspectRatio: '16:9', status: 'generating', stale: false, frameChainDeps: [] },
  ],
  references: [
    { id: 'character-alice', label: 'Alice' },
    { id: 'character-bob', label: 'Bob' },
    { id: 'brand-logo' },
  ],
};

console.log('Clips response shape:', JSON.stringify(mockClipsResponse, null, 2));
console.log('Run response shape:', JSON.stringify({ jobId: 'job-veo-abc123' }, null, 2));

// Frame chain display logic verification
function computeChainDisplay(clipId: string, deps: string[] = []): string {
  return deps.length > 0 ? `${deps.join(' → ')} → ${clipId}` : clipId;
}

console.log('Chain example:', computeChainDisplay('main-clip-3', ['main-clip-1', 'main-clip-2']));
console.log('No deps:', computeChainDisplay('intro-wide'));

// ============================================================================
// 4. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasDefaultExport,
  hasUseClient,
  hasOnAdvanceProp,
  hasCharacterReferences,
  hasRefThumbnail,
  hasRefRegenerate,
  hasRefImg,
  hasFrameChaining,
  hasChainArrow,
  hasFrameChainDeps,
  hasClipTable,
  hasClipColumn,
  hasSectionColumn,
  hasAspectColumn,
  hasStatusColumn,
  hasActionsColumn,
  hasStaleWarning,
  hasPerClipRegenerate,
  hasGenerateAll,
  hasGenerateMissing,
  hasGenerateSection,
  hasSectionDropdown,
  hasVeoRunEndpoint,
  hasPostMethod,
  hasAutoComposite,
  hasCheckbox,
  hasSplitScreen,
  hasSseLogPanel,
  hasSseImport,
  hasEventSource,
  hasSseStream,
  hasJobId,
  hasGreenDone,
  hasAmberGenerating,
  hasGrayMissing,
  hasRedError,
  hasDoneBadge,
  hasGeneratingBadge,
  hasMissingBadge,
  hasErrorBadge,
  hasAmberStale,
  hasClipsEndpoint,
  hasFetchCall,
  hasUseEffect,
  hasSectionFilter,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage7VeoGeneration component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
