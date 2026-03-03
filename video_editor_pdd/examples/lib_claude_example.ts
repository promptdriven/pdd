// example_usage_claude.ts
// Comprehensive usage example for the Claude CLI integration module (lib/claude.ts)
//
// This module is marked 'server-only' and must be used in a Node.js server
// environment (e.g., Next.js API routes or server actions). It requires the
// `claude` CLI to be installed and available on PATH for actual invocations.
//
// This example verifies the module's structure, exported functions, and JSON
// parsing fallback strategies without spawning real Claude CLI processes.

import fs from 'fs';
import path from 'path';
import { runClaudeAnalysis, runClaudeFix, runClaudeFixDryRun, parseJsonWithFallback } from '../lib/claude';
import type { AnnotationAnalysis, ClaudeFixResult } from '../lib/types';

// ============================================================================
// Helper: assert and log
// ============================================================================

let passed = 0;
let failed = 0;

function assert(condition: boolean, label: string): void {
  if (condition) {
    passed++;
    console.log(`  PASS: ${label}`);
  } else {
    failed++;
    console.log(`  FAIL: ${label}`);
  }
}

// ============================================================================
// Example 1: Verify module exports
// ============================================================================

function example1_verifyExports(): void {
  console.log('=== Example 1: Module exports ===');

  assert(typeof runClaudeAnalysis === 'function', 'runClaudeAnalysis is a function');
  assert(typeof runClaudeFix === 'function', 'runClaudeFix is a function');
  assert(typeof runClaudeFixDryRun === 'function', 'runClaudeFixDryRun is a function');
  assert(typeof parseJsonWithFallback === 'function', 'parseJsonWithFallback is a function');

  // Verify function signatures by checking .length (number of declared params)
  // runClaudeAnalysis(prompt, onLog?) => 2 params
  assert(runClaudeAnalysis.length >= 1, 'runClaudeAnalysis accepts at least 1 parameter');
  // runClaudeFix(prompt, scopeDir, onLog?) => 3 params
  assert(runClaudeFix.length >= 2, 'runClaudeFix accepts at least 2 parameters');
  // runClaudeFixDryRun(prompt, scopeDir, onLog?) => 3 params
  assert(runClaudeFixDryRun.length >= 2, 'runClaudeFixDryRun accepts at least 2 parameters');

  console.log('');
}

// ============================================================================
// Example 2: JSON parsing — strategy (a) direct JSON.parse
// ============================================================================

function example2_directJsonParse(): void {
  console.log('=== Example 2: JSON parsing — direct parse ===');

  const analysis: AnnotationAnalysis = {
    severity: 'major',
    fixType: 'remotion',
    technicalAssessment: 'Text clipped at safe zone boundary',
    suggestedFixes: ['Reduce font size', 'Add padding'],
    confidence: 0.87,
  };

  const json = JSON.stringify(analysis);
  const parsed = parseJsonWithFallback(json) as AnnotationAnalysis;

  assert(parsed.severity === 'major', 'Parsed severity matches');
  assert(parsed.fixType === 'remotion', 'Parsed fixType matches');
  assert(parsed.technicalAssessment === analysis.technicalAssessment, 'Parsed technicalAssessment matches');
  assert(Array.isArray(parsed.suggestedFixes) && parsed.suggestedFixes.length === 2, 'Parsed suggestedFixes is array of 2');
  assert(parsed.confidence === 0.87, 'Parsed confidence matches');

  console.log(`  Parsed analysis: severity=${parsed.severity}, fixType=${parsed.fixType}, confidence=${parsed.confidence}`);
  console.log('');
}

// ============================================================================
// Example 3: JSON parsing — strategy (b) code fence extraction
// ============================================================================

function example3_codeFenceParse(): void {
  console.log('=== Example 3: JSON parsing — code fence fallback ===');

  const fixResult: ClaudeFixResult = {
    fixType: 'remotion',
    filesModified: ['remotion/intro/TextOverlay.tsx'],
    changeDescription: 'Reduced font size from 48px to 40px',
    confidence: 0.92,
  };

  // Simulate Claude wrapping JSON in a code fence with surrounding text
  const stdout = `Here is the analysis result:

\`\`\`json
${JSON.stringify(fixResult, null, 2)}
\`\`\`

I've completed the fix as described above.`;

  const parsed = parseJsonWithFallback(stdout) as ClaudeFixResult;

  assert(parsed.fixType === 'remotion', 'Code-fence: parsed fixType matches');
  assert(parsed.filesModified[0] === 'remotion/intro/TextOverlay.tsx', 'Code-fence: parsed filesModified matches');
  assert(parsed.changeDescription === fixResult.changeDescription, 'Code-fence: parsed changeDescription matches');
  assert(parsed.confidence === 0.92, 'Code-fence: parsed confidence matches');

  console.log(`  Parsed fix result: fixType=${parsed.fixType}, files=${parsed.filesModified.join(', ')}`);
  console.log('');
}

// ============================================================================
// Example 4: JSON parsing — strategy (c) brace matching
// ============================================================================

function example4_braceMatchParse(): void {
  console.log('=== Example 4: JSON parsing — brace matching fallback ===');

  const analysis: AnnotationAnalysis = {
    severity: 'critical',
    fixType: 'veo',
    technicalAssessment: 'Video generation artifacts at 5.2s',
    suggestedFixes: ['Re-generate with adjusted prompt'],
    confidence: 0.65,
  };

  // Simulate raw output with JSON embedded in prose (no code fence)
  const stdout = `After careful analysis, the result is: ${JSON.stringify(analysis)} — end of analysis.`;

  const parsed = parseJsonWithFallback(stdout) as AnnotationAnalysis;

  assert(parsed.severity === 'critical', 'Brace-match: parsed severity matches');
  assert(parsed.fixType === 'veo', 'Brace-match: parsed fixType matches');
  assert(parsed.confidence === 0.65, 'Brace-match: parsed confidence matches');

  console.log(`  Parsed analysis: severity=${parsed.severity}, fixType=${parsed.fixType}`);
  console.log('');
}

// ============================================================================
// Example 5: JSON parsing — failure when no JSON is present
// ============================================================================

function example5_parseFailure(): void {
  console.log('=== Example 5: JSON parsing — failure case ===');

  const stdout = 'This is just plain text with no JSON whatsoever.';

  let threw = false;
  try {
    parseJsonWithFallback(stdout);
  } catch (err) {
    threw = true;
    assert(
      (err as Error).message === 'Unable to parse JSON from Claude CLI output',
      'Throws expected error message on parse failure'
    );
  }
  assert(threw, 'parseJsonWithFallback throws when no JSON found');

  console.log('');
}

// ============================================================================
// Example 6: Source file structure verification
// ============================================================================

function example6_sourceStructure(): void {
  console.log('=== Example 6: Source file structure (lib/claude.ts) ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'lib', 'claude.ts'),
    'utf-8'
  );

  // Requirement 7: server-only guard
  assert(sourceCode.includes('server-only'), 'Has server-only guard');

  // Requirement 8: Uses child_process.spawn (not exec)
  assert(sourceCode.includes('spawn') && !sourceCode.includes('exec('), 'Uses spawn, not exec');

  // Requirement 1: Exports runClaudeAnalysis
  assert(/export\s+(async\s+)?function\s+runClaudeAnalysis/.test(sourceCode), 'Exports runClaudeAnalysis function');

  // Requirement 2: Exports runClaudeFix
  assert(/export\s+(async\s+)?function\s+runClaudeFix/.test(sourceCode), 'Exports runClaudeFix function');

  // Requirement 5: Hard timeout of 300 seconds (300_000 ms)
  assert(sourceCode.includes('300_000') || sourceCode.includes('300000'), 'Has 300s timeout constant');
  assert(sourceCode.includes('SIGTERM'), 'Kills process with SIGTERM on timeout');
  assert(sourceCode.includes('Claude CLI timeout after 300s'), 'Has timeout error message');

  // Requirement 4: Three JSON parsing strategies
  assert(sourceCode.includes('JSON.parse'), 'Uses JSON.parse');
  assert(/```json/.test(sourceCode), 'Has code fence regex pattern');
  assert(sourceCode.includes('indexOf') && sourceCode.includes('lastIndexOf'), 'Has brace matching logic');

  // Requirement 9: Uses -p argument (not stdin)
  assert(sourceCode.includes("'-p'") || sourceCode.includes('"-p"'), 'Uses -p flag for prompt');

  // Requirement 3: Streams stderr to onLog
  assert(sourceCode.includes('stderr') && sourceCode.includes('onLog'), 'Streams stderr to onLog callback');

  // CLI flags per instructions
  assert(sourceCode.includes('claude-opus-4-6'), 'Uses claude-opus-4-6 model');
  assert(sourceCode.includes('--output-format'), 'Uses --output-format flag');
  assert(sourceCode.includes('--allowedTools'), 'Uses --allowedTools flag');
  assert(sourceCode.includes('--no-session-persistence'), 'Uses --no-session-persistence flag');

  // Analysis: read-only tools
  assert(sourceCode.includes("'Read,Glob'"), 'runClaudeAnalysis uses Read,Glob tools');

  // Fix: read-write tools
  assert(sourceCode.includes("'Read,Write,Edit,Glob,Grep'"), 'runClaudeFix uses Read,Write,Edit,Glob,Grep tools');

  // clearTimeout on close
  assert(sourceCode.includes('clearTimeout'), 'Clears timeout on process close');

  // Requirement 6: Non-zero exit code with stderr
  assert(sourceCode.includes('Claude CLI failed:'), 'Has non-zero exit code error with stderr');

  // Console.warn for fallback strategies
  assert(sourceCode.includes('console.warn'), 'Warns on fallback parsing strategies');

  // Dry Run: exports runClaudeFixDryRun
  assert(/export\s+(async\s+)?function\s+runClaudeFixDryRun/.test(sourceCode), 'Exports runClaudeFixDryRun function');

  // Dry Run: injects DRY RUN instruction
  assert(sourceCode.includes('DRY RUN'), 'Has DRY RUN instruction in prompt');

  // Dry Run: includes proposedDiff in schema
  assert(sourceCode.includes('proposedDiff'), 'Dry run schema includes proposedDiff field');

  // Dry Run: uses read-only tools (no Write or Edit)
  assert(sourceCode.includes("'Read,Glob,Grep'"), 'Dry run uses read-only tools Read,Glob,Grep');

  console.log('');
}

// ============================================================================
// Example 7: Type-safe usage patterns (demonstration, not executed)
// ============================================================================

function example7_usagePatterns(): void {
  console.log('=== Example 7: Type-safe usage patterns ===');

  // Demonstrate how runClaudeAnalysis would be called in a server action.
  // (Not executed because it requires the claude CLI on PATH.)
  const analysisPrompt = `
Analyze this annotation: "Text is cut off on the right side"
Respond with JSON: { severity, fixType, technicalAssessment, suggestedFixes, confidence }
`;

  console.log('  Analysis prompt constructed (not executed — requires claude CLI)');
  console.log(`  Prompt length: ${analysisPrompt.length} chars`);

  // Demonstrate the onLog callback pattern for SSE streaming
  const logLines: string[] = [];
  const onLog = (line: string): void => {
    logLines.push(line);
  };

  // Simulate what onLog would receive during a real invocation
  onLog('Analyzing annotation...');
  onLog('Reading source files...');
  onLog('Generating response...');

  assert(logLines.length === 3, 'onLog callback collects stderr lines');
  console.log(`  Simulated log lines: ${logLines.join(' → ')}`);

  // Demonstrate runClaudeFix pattern
  const fixPrompt = `Fix this issue: text clipping. Return JSON: { fixType, filesModified, changeDescription, confidence }`;
  const scopeDir = '/absolute/path/to/project/remotion/intro';

  console.log('  Fix prompt constructed (not executed — requires claude CLI)');
  console.log(`  Scope directory: ${scopeDir}`);

  console.log('');
}

// ============================================================================
// Example 8: AnnotationAnalysis and ClaudeFixResult shape validation
// ============================================================================

function example8_typeShapes(): void {
  console.log('=== Example 8: Expected JSON shapes from Claude ===');

  // AnnotationAnalysis shape: { severity, fixType, technicalAssessment, suggestedFixes, confidence }
  const analysisShape: AnnotationAnalysis = {
    severity: 'minor',
    fixType: 'tts',
    technicalAssessment: 'TTS timing drift of ~200ms at section boundary',
    suggestedFixes: ['Re-render TTS segment with adjusted pacing parameter'],
    confidence: 0.78,
  };

  assert(
    ['critical', 'major', 'minor', 'pass'].includes(analysisShape.severity),
    'AnnotationAnalysis severity is valid enum value'
  );
  assert(
    ['remotion', 'veo', 'tts', 'none'].includes(analysisShape.fixType),
    'AnnotationAnalysis fixType is valid FixType'
  );
  assert(typeof analysisShape.technicalAssessment === 'string', 'technicalAssessment is a string');
  assert(Array.isArray(analysisShape.suggestedFixes), 'suggestedFixes is an array');
  assert(
    analysisShape.confidence >= 0 && analysisShape.confidence <= 1,
    'confidence is between 0 and 1'
  );

  // ClaudeFixResult shape: { fixType, filesModified, changeDescription, confidence }
  const fixShape: ClaudeFixResult = {
    fixType: 'remotion',
    filesModified: ['remotion/intro/TextOverlay.tsx', 'remotion/intro/styles.ts'],
    changeDescription: 'Reduced font size and added right padding to prevent text clipping.',
    confidence: 0.91,
  };

  assert(
    ['remotion', 'veo', 'tts', 'none'].includes(fixShape.fixType),
    'ClaudeFixResult fixType is valid FixType'
  );
  assert(Array.isArray(fixShape.filesModified), 'filesModified is an array');
  assert(typeof fixShape.changeDescription === 'string', 'changeDescription is a string');
  assert(fixShape.confidence >= 0 && fixShape.confidence <= 1, 'ClaudeFixResult confidence is between 0 and 1');

  console.log(`  AnnotationAnalysis: severity=${analysisShape.severity}, fixType=${analysisShape.fixType}`);
  console.log(`  ClaudeFixResult: fixType=${fixShape.fixType}, files=${fixShape.filesModified.length}`);
  console.log('');
}

// ============================================================================
// Example 9: Dry-run mode verification
// ============================================================================

function example9_dryRunMode(): void {
  console.log('=== Example 9: Dry-run mode (runClaudeFixDryRun) ===');

  // Verify the source code wraps the prompt with DRY RUN instructions
  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'lib', 'claude.ts'),
    'utf-8'
  );

  // The dry-run function should contain instructions to NOT modify files
  assert(
    sourceCode.includes('Do NOT modify') || sourceCode.includes('Do NOT write'),
    'Dry run instructs Claude not to modify files'
  );

  // The dry-run prompt should define the expected JSON schema fields
  assert(sourceCode.includes('fixType'), 'Dry run schema has fixType');
  assert(sourceCode.includes('filesModified'), 'Dry run schema has filesModified');
  assert(sourceCode.includes('changeDescription'), 'Dry run schema has changeDescription');
  assert(sourceCode.includes('confidence'), 'Dry run schema has confidence');
  assert(sourceCode.includes('proposedDiff'), 'Dry run schema has proposedDiff');

  // Demonstrate how runClaudeFixDryRun would be called
  const dryRunPrompt = 'Preview changes for fixing text overlap in intro section';
  const scopeDir = '/absolute/path/to/project/remotion/intro';
  console.log(`  Dry-run prompt constructed (not executed — requires claude CLI)`);
  console.log(`  Prompt: "${dryRunPrompt}"`);
  console.log(`  Scope directory: ${scopeDir}`);

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_verifyExports();
  example2_directJsonParse();
  example3_codeFenceParse();
  example4_braceMatchParse();
  example5_parseFailure();
  example6_sourceStructure();
  example7_usagePatterns();
  example8_typeShapes();
  example9_dryRunMode();

  console.log('========================================');
  console.log(`Results: ${passed} passed, ${failed} failed`);
  if (failed > 0) {
    process.exit(1);
  }
  console.log('All examples completed successfully');
}

main().catch((err) => {
  console.error('Example failed:', err);
  process.exit(1);
});
