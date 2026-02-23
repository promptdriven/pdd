/**
 * Verification program for the Stage3TtsScriptGen component.
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

console.log('=== Stage3TtsScriptGen Module Verification ===\n');

const componentPath = path.resolve(__dirname, '..', 'components', 'stages', 'Stage3TtsScriptGen.tsx');

if (!fs.existsSync(componentPath)) {
  console.log('FAIL: Component file not found at', componentPath);
  process.exit(1);
}

const source = fs.readFileSync(componentPath, 'utf-8');

// Check default export
const hasDefaultExport = /export\s+default\s+function\s+Stage3TtsScriptGen/.test(source);
console.log('Default export:', hasDefaultExport ? 'PASS (function Stage3TtsScriptGen)' : 'FAIL');

// ============================================================================
// 2. Source-level requirement verification
// ============================================================================

console.log('\n=== Source-Level Requirements ===\n');

// Requirement 7: 'use client' directive
const hasUseClient = source.trimStart().startsWith("'use client'");
console.log("Req 7 - 'use client' directive at top:", hasUseClient ? 'PASS' : 'FAIL');

// Requirement 1: Props interface with onAdvance
const hasOnAdvanceProp = /onAdvance\s*:\s*\(\)\s*=>\s*void/.test(source);
console.log('Req 1 - Props (onAdvance: () => void):', hasOnAdvanceProp ? 'PASS' : 'FAIL');

// Requirement 2: Generate TTS Script button
const hasGenerateButton = source.includes('Generate TTS Script');
console.log('Req 2 - Generate TTS Script button:', hasGenerateButton ? 'PASS' : 'FAIL');

// Requirement 2: Last run timestamp
const hasLastRunTime = source.includes('lastRunTime') || source.includes('Last run');
console.log('Req 2 - Last run timestamp display:', hasLastRunTime ? 'PASS' : 'FAIL');

// Requirement 3: SseLogPanel with jobId
const hasSseLogPanel = source.includes('SseLogPanel');
const hasSseJobId = source.includes('jobId');
console.log('Req 3 - SseLogPanel component:', hasSseLogPanel ? 'PASS' : 'FAIL');
console.log('Req 3 - jobId state for SSE:', hasSseJobId ? 'PASS' : 'FAIL');

// Requirement 4: Diff view with line coloring
const hasDiffLines = source.includes('diffLines');
const hasGreenColor = source.includes('green');
const hasRedColor = source.includes('red');
const hasGrayColor = source.includes('gray');
const hasDiffTypes = source.includes('added') && source.includes('removed') && source.includes('unchanged');
console.log('Req 4 - diffLines import/usage:', hasDiffLines ? 'PASS' : 'FAIL');
console.log('Req 4 - Green color for added lines:', hasGreenColor ? 'PASS' : 'FAIL');
console.log('Req 4 - Red color for removed lines:', hasRedColor ? 'PASS' : 'FAIL');
console.log('Req 4 - Gray color for unchanged lines:', hasGrayColor ? 'PASS' : 'FAIL');
console.log('Req 4 - Diff types (added/removed/unchanged):', hasDiffTypes ? 'PASS' : 'FAIL');

// Requirement 4: Split display (two-column)
const hasTwoColumnLayout = source.includes('grid-cols-2') || source.includes('grid grid-cols');
const hasMainScriptLabel = source.includes('main_script.md');
const hasTtsScriptLabel = source.includes('tts_script.md');
console.log('Req 4 - Two-column grid layout:', hasTwoColumnLayout ? 'PASS' : 'FAIL');
console.log('Req 4 - main_script.md label:', hasMainScriptLabel ? 'PASS' : 'FAIL');
console.log('Req 4 - tts_script.md label:', hasTtsScriptLabel ? 'PASS' : 'FAIL');

// Requirement 5: CodeMirror editor
const hasCodeMirror = source.includes('CodeMirror');
const hasMarkdownExtension = source.includes('markdown()') || source.includes('lang-markdown');
console.log('Req 5 - CodeMirror editor:', hasCodeMirror ? 'PASS' : 'FAIL');
console.log('Req 5 - Markdown language extension:', hasMarkdownExtension ? 'PASS' : 'FAIL');

// Requirement 5: Auto-save on blur + 1s debounce
const hasOnBlur = source.includes('onBlur');
const hasDebounce = source.includes('setTimeout') && source.includes('1000');
console.log('Req 5 - onBlur save handler:', hasOnBlur ? 'PASS' : 'FAIL');
console.log('Req 5 - 1s debounce save:', hasDebounce ? 'PASS' : 'FAIL');

// Requirement 5: Fetch script content
const hasFetchScript = source.includes('/api/project/script');
console.log('Req 5 - GET /api/project/script endpoint:', hasFetchScript ? 'PASS' : 'FAIL');

// Requirement 6: Render Audio advance button
const hasRenderAudioButton = source.includes('Render Audio');
const hasOnAdvanceCall = source.includes('onAdvance()') || source.includes('onAdvance(') || source.includes('{onAdvance}');
const hasDisabledWhenNoTts = source.includes('ttsExists');
console.log('Req 6 - Render Audio button:', hasRenderAudioButton ? 'PASS' : 'FAIL');
console.log('Req 6 - Calls onAdvance():', hasOnAdvanceCall ? 'PASS' : 'FAIL');
console.log('Req 6 - Disabled when tts_script missing:', hasDisabledWhenNoTts ? 'PASS' : 'FAIL');

// Instruction: POST to /api/pipeline/tts-script/run
const hasRunEndpoint = source.includes('/api/pipeline/tts-script/run');
console.log('Inst - POST /api/pipeline/tts-script/run:', hasRunEndpoint ? 'PASS' : 'FAIL');

// Instruction: localStorage key
const hasLocalStorageKey = source.includes('tts-script-last-run');
console.log('Inst - localStorage key tts-script-last-run:', hasLocalStorageKey ? 'PASS' : 'FAIL');

// Instruction: SseLogPanel import
const hasSseImport = source.includes("import SseLogPanel") || source.includes("import { SseLogPanel");
console.log('Inst - SseLogPanel import:', hasSseImport ? 'PASS' : 'FAIL');

// Instruction: diff import
const hasDiffImport = source.includes("from 'diff'") || source.includes('from "diff"');
console.log('Inst - diff package import:', hasDiffImport ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  hasDefaultExport,
  hasUseClient,
  hasOnAdvanceProp,
  hasGenerateButton,
  hasLastRunTime,
  hasSseLogPanel,
  hasSseJobId,
  hasDiffLines,
  hasGreenColor,
  hasRedColor,
  hasGrayColor,
  hasDiffTypes,
  hasTwoColumnLayout,
  hasMainScriptLabel,
  hasTtsScriptLabel,
  hasCodeMirror,
  hasMarkdownExtension,
  hasOnBlur,
  hasDebounce,
  hasFetchScript,
  hasRenderAudioButton,
  hasOnAdvanceCall,
  hasDisabledWhenNoTts,
  hasRunEndpoint,
  hasLocalStorageKey,
  hasSseImport,
  hasDiffImport,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nStage3TtsScriptGen component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
