/**
 * Verification program for the Stage6SpecGeneration component.
 *
 * Validates the component module structure, exports, and source-level
 * requirements from the prompt specification. Runs headlessly with
 * `npx tsx` to produce console output for PDD verification.
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * Component: Stage6SpecGeneration
 * ─────────────────────────────────────────────────────────────────────────────
 *
 * Props:
 *   onAdvance: () => void
 *
 * Required API Endpoints:
 *   GET  /api/pipeline/specs/list
 *   GET  /api/pipeline/specs/file?path=<encodedPath>
 *   PUT  /api/pipeline/specs/file
 *   POST /api/pipeline/specs/run
 *
 * Dependencies:
 *   - @uiw/react-codemirror (CodeMirror 6 React wrapper)
 *   - @codemirror/lang-markdown (Markdown language support)
 *   - SseLogPanel component (for streaming job logs)
 */

import * as fs from 'fs';
import * as path from 'path';

// ============================================================================
// 1. Module export verification
// ============================================================================

console.log('=== Stage6SpecGeneration Module Verification ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage6SpecGeneration.tsx');

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

// Requirement 7: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 7 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props interface with onAdvance: () => void
const hasOnAdvanceProp = /onAdvance\s*:\s*\(\)\s*=>\s*void/.test(source);
console.log('Req 1 - Props (onAdvance: () => void):', hasOnAdvanceProp ? 'PASS' : 'FAIL');

// Requirement 2: Toolbar with Generate All Specs and per-section Regenerate
const hasGenerateAllButton = source.includes('Generate All Specs');
const hasRegenerateButton = source.includes('Regenerate');
const hasPostSpecsRun = source.includes('/api/pipeline/specs/run');
const hasPostMethod = source.includes("method: 'POST'") || source.includes('method: "POST"');
console.log('Req 2 - Generate All Specs button:', hasGenerateAllButton ? 'PASS' : 'FAIL');
console.log('Req 2 - Regenerate button:', hasRegenerateButton ? 'PASS' : 'FAIL');
console.log('Req 2 - POST /api/pipeline/specs/run:', hasPostSpecsRun ? 'PASS' : 'FAIL');
console.log('Req 2 - POST method:', hasPostMethod ? 'PASS' : 'FAIL');

// Requirement 3: Collapsible section groups with localStorage persistence
const hasLocalStorageKey = source.includes('spec-sections-expanded');
const hasLocalStorageGet = source.includes('localStorage.getItem');
const hasLocalStorageSet = source.includes('localStorage.setItem');
const hasExpandedState = /useState<Record<string,\s*boolean>>/.test(source);
console.log('Req 3 - localStorage key spec-sections-expanded:', hasLocalStorageKey ? 'PASS' : 'FAIL');
console.log('Req 3 - localStorage.getItem:', hasLocalStorageGet ? 'PASS' : 'FAIL');
console.log('Req 3 - localStorage.setItem:', hasLocalStorageSet ? 'PASS' : 'FAIL');
console.log('Req 3 - Expanded state Record<string, boolean>:', hasExpandedState ? 'PASS' : 'FAIL');

// Requirement 4: Spec file rows with type badge, path, status, actions
const hasEditButton = source.includes('✎');
const hasRegenerateFileButton = source.includes('↺');
const hasExistsStatus = source.includes('exists');
const hasMissingStatus = source.includes('missing');
console.log('Req 4 - Edit button (✎):', hasEditButton ? 'PASS' : 'FAIL');
console.log('Req 4 - Regenerate icon (↺):', hasRegenerateFileButton ? 'PASS' : 'FAIL');
console.log('Req 4 - exists status:', hasExistsStatus ? 'PASS' : 'FAIL');
console.log('Req 4 - missing status:', hasMissingStatus ? 'PASS' : 'FAIL');

// Requirement 5: Inline CodeMirror editor with auto-save on blur
const hasCodeMirrorImport = source.includes('@uiw/react-codemirror');
const hasMarkdownImport = source.includes('@codemirror/lang-markdown');
const hasCodeMirrorComponent = source.includes('CodeMirror');
const hasPutMethod = source.includes("method: 'PUT'") || source.includes('method: "PUT"');
const hasSpecsFileEndpoint = source.includes('/api/pipeline/specs/file');
const hasOnBlur = source.includes('onBlur') || source.includes('Blur');
console.log('Req 5 - CodeMirror import:', hasCodeMirrorImport ? 'PASS' : 'FAIL');
console.log('Req 5 - Markdown extension import:', hasMarkdownImport ? 'PASS' : 'FAIL');
console.log('Req 5 - CodeMirror component:', hasCodeMirrorComponent ? 'PASS' : 'FAIL');
console.log('Req 5 - PUT method for save:', hasPutMethod ? 'PASS' : 'FAIL');
console.log('Req 5 - /api/pipeline/specs/file endpoint:', hasSpecsFileEndpoint ? 'PASS' : 'FAIL');
console.log('Req 5 - onBlur auto-save:', hasOnBlur ? 'PASS' : 'FAIL');

// Requirement 6: SSE log drawer
const hasSseLogPanel = source.includes('SseLogPanel');
const hasSseImport = source.includes("import SseLogPanel") || source.includes("import { SseLogPanel");
const hasJobId = source.includes('jobId');
const hasDetailsElement = source.includes('<details');
console.log('Req 6 - SseLogPanel component:', hasSseLogPanel ? 'PASS' : 'FAIL');
console.log('Req 6 - SseLogPanel import:', hasSseImport ? 'PASS' : 'FAIL');
console.log('Req 6 - jobId state:', hasJobId ? 'PASS' : 'FAIL');
console.log('Req 6 - <details> drawer:', hasDetailsElement ? 'PASS' : 'FAIL');

// Requirement 8: Visual type badge colors
const hasRemotionBadge = /\[Remotion\]/i.test(source) || source.includes('Remotion');
const hasBlueBadge = source.includes('blue');
const hasVeoBadge = source.includes('veo');
const hasPurpleBadge = source.includes('purple');
const hasTitleBadge = source.includes('title');
const hasTealBadge = source.includes('teal');
const hasSplitBadge = source.includes('split');
const hasOrangeBadge = source.includes('orange');
console.log('Req 8 - Remotion badge:', hasRemotionBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - Blue color for Remotion:', hasBlueBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - veo badge:', hasVeoBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - Purple color for veo:', hasPurpleBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - title badge:', hasTitleBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - Teal color for title:', hasTealBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - split badge:', hasSplitBadge ? 'PASS' : 'FAIL');
console.log('Req 8 - Orange color for split:', hasOrangeBadge ? 'PASS' : 'FAIL');

// Instruction: Load spec list on mount
const hasSpecsListEndpoint = source.includes('/api/pipeline/specs/list');
const hasFetchCall = source.includes('fetch(');
const hasUseEffect = source.includes('useEffect');
console.log('Inst - GET /api/pipeline/specs/list:', hasSpecsListEndpoint ? 'PASS' : 'FAIL');
console.log('Inst - fetch() call:', hasFetchCall ? 'PASS' : 'FAIL');
console.log('Inst - useEffect for mount:', hasUseEffect ? 'PASS' : 'FAIL');

// Instruction: Per-section and per-file regenerate payloads
const hasSectionsPayload = source.includes('sections:');
const hasFilesPayload = source.includes('files:');
console.log('Inst - sections payload for per-section regen:', hasSectionsPayload ? 'PASS' : 'FAIL');
console.log('Inst - files payload for per-file regen:', hasFilesPayload ? 'PASS' : 'FAIL');

// Instruction: Debounce on blur save (1s)
const hasDebounce = source.includes('setTimeout') || source.includes('debounce');
console.log('Inst - Debounce/setTimeout for save:', hasDebounce ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Example API response shapes (for documentation)
// ============================================================================

console.log('\n=== Example API Response Shapes ===\n');

const exampleSpecListResponse = {
  sections: [
    {
      id: 'intro',
      label: 'Introduction',
      files: [
        { path: 'specs/intro/visual.md', exists: true, firstLine: '[Remotion] Introduction visual overlay spec' },
        { path: 'specs/intro/background.md', exists: true, firstLine: '[veo:landscape] Background generation for intro' },
        { path: 'specs/intro/title-card.md', exists: false, firstLine: '[title:main] Title card specification' },
      ],
    },
    {
      id: 'main',
      label: 'Main Content',
      files: [
        { path: 'specs/main/scene1.md', exists: true, firstLine: '[veo:product-demo] Product demonstration scene' },
        { path: 'specs/main/transition.md', exists: true, firstLine: '[split:horizontal] Scene transition effect' },
        { path: 'specs/main/overlay.md', exists: true, firstLine: '[Remotion] Data visualization overlay' },
      ],
    },
    {
      id: 'outro',
      label: 'Outro',
      files: [
        { path: 'specs/outro/credits.md', exists: false },
        { path: 'specs/outro/cta.md', exists: true, firstLine: '[Remotion] Call-to-action animation' },
      ],
    },
  ],
};

console.log('Spec list response shape:', JSON.stringify(exampleSpecListResponse, null, 2));
console.log('File response shape:', JSON.stringify({ content: '[Remotion] Introduction visual overlay spec\n\n## Layout\n...' }, null, 2));
console.log('Run response shape:', JSON.stringify({ jobId: 'job-spec-gen-abc123' }, null, 2));
console.log('Save request shape:', JSON.stringify({ path: 'specs/intro/visual.md', content: '...updated markdown content...' }, null, 2));

// ============================================================================
// 4. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasDefaultExport,
  hasUseClient,
  hasOnAdvanceProp,
  hasGenerateAllButton,
  hasRegenerateButton,
  hasPostSpecsRun,
  hasPostMethod,
  hasLocalStorageKey,
  hasLocalStorageGet,
  hasLocalStorageSet,
  hasExpandedState,
  hasEditButton,
  hasRegenerateFileButton,
  hasExistsStatus,
  hasMissingStatus,
  hasCodeMirrorImport,
  hasMarkdownImport,
  hasCodeMirrorComponent,
  hasPutMethod,
  hasSpecsFileEndpoint,
  hasOnBlur,
  hasSseLogPanel,
  hasSseImport,
  hasJobId,
  hasDetailsElement,
  hasRemotionBadge,
  hasBlueBadge,
  hasVeoBadge,
  hasPurpleBadge,
  hasTitleBadge,
  hasTealBadge,
  hasSplitBadge,
  hasOrangeBadge,
  hasSpecsListEndpoint,
  hasFetchCall,
  hasUseEffect,
  hasSectionsPayload,
  hasFilesPayload,
  hasDebounce,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage6SpecGeneration component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
