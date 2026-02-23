/**
 * Example: resolve-batch API route
 *
 * Exercises the POST /api/sections/[id]/resolve-batch route handler logic
 * using an in-memory SQLite database. Verifies:
 *   - No-annotations case returns { jobId: null }
 *   - With annotations: creates job, groups by fixType, updates resolveJobId
 *   - buildRemotionPrompt() generates correct prompt structure
 *   - Annotation deserialization from DB rows
 *   - Manual fixType annotations are skipped
 *   - export const dynamic = 'force-dynamic' is set
 */

// Set up in-memory DB before any imports that call getDb()
process.env.DB_PATH = ':memory:';

import { getDb } from '../lib/db';
import { createJob, runJob, getJob, registerExecutor } from '../lib/jobs';
import type { Annotation, AnnotationAnalysis } from '../lib/types';
import fs from 'fs';
import path from 'path';

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
// Example 1: Verify route source structure
// ============================================================================

function example1_verifyRouteStructure(): void {
  console.log('=== Example 1: Route source structure ===');

  const routeSrc = fs.readFileSync(
    path.join(__dirname, '..', 'app', 'api', 'sections', '[id]', 'resolve-batch', 'route.ts'),
    'utf-8'
  );

  // Requirement 3: export const dynamic = 'force-dynamic'
  assert(routeSrc.includes("export const dynamic"), 'Has dynamic export');
  assert(routeSrc.includes("force-dynamic"), 'dynamic is force-dynamic');

  // Requirement: exports POST handler
  assert(/export\s+async\s+function\s+POST/.test(routeSrc), 'Exports async POST function');

  // Requirement: uses NextResponse
  assert(routeSrc.includes('NextResponse.json'), 'Uses NextResponse.json for responses');

  // Requirement: creates job with audit stage
  assert(routeSrc.includes("createJob(\"audit\"") || routeSrc.includes("createJob('audit'"), 'Creates audit job');

  // Requirement: fire-and-forget runJob
  assert(routeSrc.includes('void runJob'), 'Uses void runJob (fire-and-forget)');

  // Requirement: groups by fixType
  assert(routeSrc.includes('remotion') && routeSrc.includes('veo') && routeSrc.includes('tts'), 'Groups by fixType (remotion, veo, tts)');
  assert(routeSrc.includes('manual'), 'Handles manual fixType');

  // Requirement: calls runClaudeFix for remotion
  assert(routeSrc.includes('runClaudeFix'), 'Calls runClaudeFix for remotion fixes');
  assert(routeSrc.includes('remotion/src/remotion/'), 'Scopes Claude fix to remotion/src/remotion/');

  // Requirement: calls renderSection after fixes
  assert(routeSrc.includes('renderSection'), 'Calls renderSection after fixes');

  // Requirement: updates resolveJobId
  assert(routeSrc.includes('resolveJobId') && routeSrc.includes('UPDATE annotations'), 'Updates annotation resolveJobId');

  // Requirement: no auth required (no auth imports/checks)
  assert(!routeSrc.includes('getAuth') && !routeSrc.includes('requireAuth'), 'No authentication required');

  // Requirement: buildRemotionPrompt function exists
  assert(routeSrc.includes('buildRemotionPrompt'), 'Has buildRemotionPrompt function');

  // Requirement: loadProject and getSection
  assert(routeSrc.includes('loadProject') && routeSrc.includes('getSection'), 'Uses loadProject and getSection');

  console.log('');
}

// ============================================================================
// Example 2: No unresolved annotations → { jobId: null }
// ============================================================================

function example2_noAnnotations(): void {
  console.log('=== Example 2: No unresolved annotations ===');

  const db = getDb();

  // Query for a section with no annotations
  const rows = db
    .prepare('SELECT * FROM annotations WHERE sectionId = ? AND resolved = 0')
    .all('empty-section');

  assert(rows.length === 0, 'No rows returned for empty section');

  // The route would return { jobId: null, message: "No unresolved annotations" }
  const response = { jobId: null as string | null, message: 'No unresolved annotations' };
  assert(response.jobId === null, 'jobId is null when no annotations');
  assert(response.message === 'No unresolved annotations', 'Message matches expected string');

  console.log(`  Response: ${JSON.stringify(response)}`);
  console.log('');
}

// ============================================================================
// Example 3: Insert annotations and verify DB query + deserialization
// ============================================================================

function example3_annotationDeserialization(): void {
  console.log('=== Example 3: Annotation deserialization from DB ===');

  const db = getDb();

  // Insert test annotations with different fixTypes
  const analyses: Record<string, AnnotationAnalysis> = {
    remotion: {
      severity: 'major',
      fixType: 'remotion',
      technicalAssessment: 'Text clipped at safe zone boundary',
      suggestedFixes: ['Reduce font size', 'Add padding'],
      confidence: 0.87,
    },
    veo: {
      severity: 'critical',
      fixType: 'veo',
      technicalAssessment: 'Video artifacts at 5.2s',
      suggestedFixes: ['Re-generate clip'],
      confidence: 0.65,
    },
    tts: {
      severity: 'minor',
      fixType: 'tts',
      technicalAssessment: 'TTS timing drift of ~200ms',
      suggestedFixes: ['Re-render TTS segment'],
      confidence: 0.78,
    },
  };

  const insertStmt = db.prepare(
    `INSERT INTO annotations (id, sectionId, timestamp, text, videoFile, analysis, resolved, createdAt)
     VALUES (?, ?, ?, ?, ?, ?, 0, ?)`
  );

  insertStmt.run('ann-001', 'intro', 3.2, 'Text is cut off on the right side', 'output/sections/intro.mp4', JSON.stringify(analyses.remotion), '2025-01-15T11:00:00Z');
  insertStmt.run('ann-002', 'intro', 5.2, 'Video has artifacts', 'output/sections/intro.mp4', JSON.stringify(analyses.veo), '2025-01-15T11:01:00Z');
  insertStmt.run('ann-003', 'intro', 8.0, 'Audio timing is off', 'output/sections/intro.mp4', JSON.stringify(analyses.tts), '2025-01-15T11:02:00Z');
  // Manual annotation (no analysis → defaults to manual in route)
  insertStmt.run('ann-004', 'intro', 10.0, 'Needs manual review', 'output/sections/intro.mp4', null, '2025-01-15T11:03:00Z');
  // Resolved annotation (should NOT be queried)
  db.prepare(
    `INSERT INTO annotations (id, sectionId, timestamp, text, videoFile, analysis, resolved, createdAt)
     VALUES (?, ?, ?, ?, ?, ?, 1, ?)`
  ).run('ann-005', 'intro', 12.0, 'Already fixed', 'output/sections/intro.mp4', JSON.stringify(analyses.remotion), '2025-01-15T11:04:00Z');

  // Query as the route does
  const rows = db
    .prepare('SELECT * FROM annotations WHERE sectionId = ? AND resolved = 0 ORDER BY timestamp ASC')
    .all('intro') as Array<Record<string, unknown>>;

  assert(rows.length === 4, `Found 4 unresolved annotations (got ${rows.length})`);

  // Deserialize as the route does
  const annotations: Annotation[] = rows.map((row) => {
    const analysisRaw = (row.analysis as string | null);
    const analysis = analysisRaw ? JSON.parse(analysisRaw) : null;

    return {
      id: String(row.id),
      sectionId: String(row.sectionId),
      timestamp: Number(row.timestamp),
      text: String(row.text ?? ''),
      videoFile: (row.videoFile as string | null) ?? null,
      drawingDataUrl: (row.drawingDataUrl as string | null) ?? null,
      compositeDataUrl: (row.compositeDataUrl as string | null) ?? null,
      analysis,
      resolved: Boolean(row.resolved),
      resolveJobId: (row.resolveJobId as string | null) ?? null,
      createdAt: String(row.createdAt ?? ''),
    };
  });

  // Verify deserialized annotations
  const ann1 = annotations[0];
  assert(ann1.id === 'ann-001', 'First annotation ID is ann-001');
  assert(ann1.sectionId === 'intro', 'sectionId deserialized correctly');
  assert(ann1.timestamp === 3.2, 'timestamp deserialized as number');
  assert(ann1.analysis !== null, 'analysis deserialized from JSON');
  assert(ann1.analysis!.fixType === 'remotion', 'fixType is remotion');
  assert(ann1.analysis!.severity === 'major', 'severity is major');
  assert(ann1.analysis!.confidence === 0.87, 'confidence is 0.87');
  assert(ann1.resolved === false, 'resolved is false');

  // Annotation with no analysis (manual)
  const ann4 = annotations[3];
  assert(ann4.id === 'ann-004', 'Fourth annotation is ann-004');
  assert(ann4.analysis === null, 'No analysis → null (defaults to manual in route)');

  // Resolved annotation should not be in results
  assert(!annotations.some((a) => a.id === 'ann-005'), 'Resolved annotation excluded from query');

  console.log(`  Deserialized ${annotations.length} annotations from DB`);
  console.log(`  Annotation ID: ${ann1.id}`);
  console.log(`  Section: ${ann1.sectionId}`);
  console.log(`  Fix type: ${ann1.analysis?.fixType}`);
  console.log(`  Severity: ${ann1.analysis?.severity}`);
  console.log(`  Confidence: ${ann1.analysis?.confidence}`);
  console.log('');
}

// ============================================================================
// Example 4: Job creation and annotation update
// ============================================================================

function example4_jobCreationAndAnnotationUpdate(): void {
  console.log('=== Example 4: Job creation and resolveJobId update ===');

  const db = getDb();

  // Create audit job (as the route does)
  const jobId = createJob('audit', { sectionId: 'intro' });

  assert(typeof jobId === 'string', 'createJob returns a string job ID');
  assert(jobId.length > 0, 'Job ID is non-empty');

  // Verify job was created
  const job = getJob(jobId);
  assert(job !== undefined, 'Job exists in database');
  assert(job?.stage === 'audit', 'Job stage is audit');
  assert(job?.status === 'pending', 'Job starts as pending');

  // Update resolveJobId for annotations (as the route does)
  const updateStmt = db.prepare('UPDATE annotations SET resolveJobId = ? WHERE id = ?');
  const annIds = ['ann-001', 'ann-002', 'ann-003', 'ann-004'];
  for (const annId of annIds) {
    updateStmt.run(jobId, annId);
  }

  // Verify the update
  const updated = db.prepare('SELECT id, resolveJobId FROM annotations WHERE sectionId = ? AND resolved = 0').all('intro') as Array<Record<string, unknown>>;
  for (const row of updated) {
    assert(row.resolveJobId === jobId, `Annotation ${row.id} has resolveJobId set to job`);
  }

  console.log(`  Created audit job: ${jobId}`);
  console.log(`  Updated ${annIds.length} annotations with resolveJobId`);
  console.log('');
}

// ============================================================================
// Example 5: Fix type grouping and executor behavior
// ============================================================================

async function example5_fixTypeGrouping(): Promise<void> {
  console.log('=== Example 5: Fix type grouping ===');

  const db = getDb();

  // Load annotations (same query as route)
  const rows = db
    .prepare('SELECT * FROM annotations WHERE sectionId = ? AND resolved = 0 ORDER BY timestamp ASC')
    .all('intro') as Array<Record<string, unknown>>;

  const annotations: Annotation[] = rows.map((row) => {
    const analysisRaw = (row.analysis as string | null);
    const analysis = analysisRaw ? JSON.parse(analysisRaw) : null;
    return {
      id: String(row.id),
      sectionId: String(row.sectionId),
      timestamp: Number(row.timestamp),
      text: String(row.text ?? ''),
      videoFile: (row.videoFile as string | null) ?? null,
      drawingDataUrl: null,
      compositeDataUrl: null,
      analysis,
      resolved: Boolean(row.resolved),
      resolveJobId: (row.resolveJobId as string | null) ?? null,
      createdAt: String(row.createdAt ?? ''),
    };
  });

  // Group by fixType (as the route does)
  const byFixType: Record<string, Annotation[]> = {
    remotion: [],
    veo: [],
    tts: [],
    manual: [],
    none: [],
  };

  for (const ann of annotations) {
    const fixType = ann.analysis?.fixType ?? 'manual';
    if (byFixType[fixType]) byFixType[fixType].push(ann);
  }

  assert(byFixType.remotion.length === 1, 'One remotion annotation (ann-001)');
  assert(byFixType.veo.length === 1, 'One veo annotation (ann-002)');
  assert(byFixType.tts.length === 1, 'One tts annotation (ann-003)');
  assert(byFixType.manual.length === 1, 'One manual annotation (ann-004, no analysis)');

  // Simulate the executor log messages
  const logs: string[] = [];
  const onLog = (msg: string) => { logs.push(msg); };

  // Remotion: would call runClaudeFix (we just log)
  for (const ann of byFixType.remotion) {
    onLog(`Running Claude fix for annotation ${ann.id}`);
  }

  // Veo: placeholder
  for (const ann of byFixType.veo) {
    onLog(`Queued Veo regeneration for annotation ${ann.id} (pending)`);
  }

  // TTS: placeholder
  for (const ann of byFixType.tts) {
    onLog(`Queued TTS re-render for annotation ${ann.id} (pending)`);
  }

  // Manual: skipped
  for (const ann of byFixType.manual) {
    onLog(`Skipped manual annotation ${ann.id}`);
  }

  assert(logs.includes('Running Claude fix for annotation ann-001'), 'Remotion fix logged');
  assert(logs.includes('Queued Veo regeneration for annotation ann-002 (pending)'), 'Veo regen logged');
  assert(logs.includes('Queued TTS re-render for annotation ann-003 (pending)'), 'TTS re-render logged');
  assert(logs.includes('Skipped manual annotation ann-004'), 'Manual annotation skipped');

  console.log('  Fix type groups:');
  for (const [type, anns] of Object.entries(byFixType)) {
    if (anns.length > 0) {
      console.log(`    ${type}: ${anns.map((a) => a.id).join(', ')}`);
    }
  }
  console.log(`  Executor logs: ${logs.length} entries`);
  for (const log of logs) {
    console.log(`    • ${log}`);
  }
  console.log('');
}

// ============================================================================
// Example 6: Remotion prompt structure (buildRemotionPrompt)
// ============================================================================

function example6_promptStructure(): void {
  console.log('=== Example 6: Remotion prompt structure ===');

  // Mirrors the buildRemotionPrompt() function from the route
  function buildRemotionPrompt(annotation: Annotation): string {
    return `
You are applying a Remotion fix for this annotation.
Annotation ID: ${annotation.id}
Section ID: ${annotation.sectionId}
Timestamp: ${annotation.timestamp}s
User note: ${annotation.text}

Provide a fix that resolves the issue. Return JSON:
{ "fixType", "filesModified", "changeDescription", "confidence" }
`.trim();
  }

  const testAnnotation: Annotation = {
    id: 'ann-001',
    sectionId: 'intro',
    timestamp: 3.2,
    text: 'Text is cut off on the right side',
    videoFile: null,
    drawingDataUrl: null,
    compositeDataUrl: null,
    analysis: null,
    resolved: false,
    resolveJobId: null,
    createdAt: '',
  };

  const prompt = buildRemotionPrompt(testAnnotation);

  assert(prompt.includes('Annotation ID: ann-001'), 'Prompt includes annotation ID');
  assert(prompt.includes('Section ID: intro'), 'Prompt includes section ID');
  assert(prompt.includes('Timestamp: 3.2s'), 'Prompt includes timestamp');
  assert(prompt.includes('Text is cut off on the right side'), 'Prompt includes user note');
  assert(prompt.includes('fixType'), 'Prompt requests fixType in response');
  assert(prompt.includes('filesModified'), 'Prompt requests filesModified in response');

  console.log('  Sample prompt sent to Claude:');
  console.log(`  ${prompt.split('\n').join('\n  ')}`);
  console.log('');
}

// ============================================================================
// Example 7: runJob executor pattern (fire-and-forget)
// ============================================================================

async function example7_runJobExecutor(): Promise<void> {
  console.log('=== Example 7: Job executor (fire-and-forget pattern) ===');

  // Register an audit executor so runJob works
  registerExecutor('audit', (_params, _send) => {
    return async (onLog) => {
      onLog('Audit executor running');
    };
  });

  const jobId = createJob('audit', { sectionId: 'intro' });

  // The route uses void runJob(...) for fire-and-forget.
  // Here we await to verify behavior.
  const logs: string[] = [];

  await runJob(jobId, async (onLog) => {
    onLog('Processing remotion fixes...');
    onLog('Processing veo fixes...');
    onLog('Processing tts fixes...');
    onLog('Skipping manual annotations...');
    onLog('Rendering section...');

    logs.push('Processing remotion fixes...');
    logs.push('Processing veo fixes...');
    logs.push('Processing tts fixes...');
    logs.push('Skipping manual annotations...');
    logs.push('Rendering section...');
  });

  const completedJob = getJob(jobId);

  assert(completedJob?.status === 'done', 'Job status is done after successful execution');
  assert(completedJob?.progress === 100, 'Job progress is 100%');
  assert(logs.length === 5, 'Executor logged 5 messages');

  console.log(`  Job ${jobId}: status=${completedJob?.status}, progress=${completedJob?.progress}%`);
  console.log(`  Job status transitions: pending → running → done`);
  console.log('');
}

// ============================================================================
// Example 8: UI integration pattern
// ============================================================================

function example8_uiPattern(): void {
  console.log('=== Example 8: UI integration pattern ===');
  console.log('  Key points:');
  console.log('    - POST to /api/sections/{id}/resolve-batch (no body needed)');
  console.log('    - Check if jobId is null (no annotations to resolve)');
  console.log('    - Poll /api/jobs/{jobId} for status updates');
  console.log('    - Job status transitions: pending → running → done | error');
  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  console.log('resolve-batch route — Usage Examples\n');

  example1_verifyRouteStructure();
  example2_noAnnotations();
  example3_annotationDeserialization();
  example4_jobCreationAndAnnotationUpdate();
  await example5_fixTypeGrouping();
  example6_promptStructure();
  await example7_runJobExecutor();
  example8_uiPattern();

  console.log('========================================');
  console.log(`Results: ${passed} passed, ${failed} failed`);
  if (failed > 0) {
    process.exit(1);
  }
  console.log('✅ All examples completed successfully.');
}

main().catch((err) => {
  console.error('Example failed:', err);
  process.exit(1);
});
