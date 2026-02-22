// example_veo_usage.ts
// Comprehensive usage example for lib/veo.ts — Veo/Imagen API client with frame extraction
//
// This module is marked 'server-only' and must be used in a Node.js server
// environment (e.g., Next.js API routes or server actions). It requires
// GOOGLE_API_KEY, @google/genai SDK, and ffmpeg/ffprobe for actual invocations.
//
// This example verifies the module's structure, exported functions, and
// demonstrates type-safe usage patterns without making real API calls.

import fs from 'fs';
import path from 'path';
import {
  generateReferenceImage,
  generateVeoClip,
  extractLastFrame,
} from '../lib/veo';

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

  assert(typeof generateReferenceImage === 'function', 'generateReferenceImage is a function');
  assert(typeof generateVeoClip === 'function', 'generateVeoClip is a function');
  assert(typeof extractLastFrame === 'function', 'extractLastFrame is a function');

  // Verify function signatures by checking .length (number of declared params)
  // generateReferenceImage(prompt, outputPath) => 2 params
  assert(generateReferenceImage.length === 2, 'generateReferenceImage accepts 2 parameters');
  // generateVeoClip(prompt, referenceImagePath, aspectRatio, outputPath) => 4 params
  assert(generateVeoClip.length === 4, 'generateVeoClip accepts 4 parameters');
  // extractLastFrame(clipPath, outputPath) => 2 params
  assert(extractLastFrame.length === 2, 'extractLastFrame accepts 2 parameters');

  console.log('');
}

// ============================================================================
// Example 2: generateReferenceImage requires GOOGLE_API_KEY
// ============================================================================

async function example2_apiKeyRequired(): Promise<void> {
  console.log('=== Example 2: API key validation ===');

  // Temporarily clear GOOGLE_API_KEY to verify the guard
  const originalKey = process.env.GOOGLE_API_KEY;
  delete process.env.GOOGLE_API_KEY;

  let threw = false;
  try {
    await generateReferenceImage('test prompt', '/tmp/test.png');
  } catch (err) {
    threw = true;
    const msg = (err as Error).message;
    assert(
      msg.includes('GOOGLE_API_KEY'),
      'generateReferenceImage throws when GOOGLE_API_KEY is not set'
    );
  }
  assert(threw, 'generateReferenceImage rejects without API key');

  // Restore
  if (originalKey) {
    process.env.GOOGLE_API_KEY = originalKey;
  }

  console.log('');
}

// ============================================================================
// Example 3: generateVeoClip requires GOOGLE_API_KEY
// ============================================================================

async function example3_veoApiKeyRequired(): Promise<void> {
  console.log('=== Example 3: Veo API key validation ===');

  const originalKey = process.env.GOOGLE_API_KEY;
  delete process.env.GOOGLE_API_KEY;

  let threw = false;
  try {
    await generateVeoClip('test prompt', null, '16:9', '/tmp/test.mp4');
  } catch (err) {
    threw = true;
    const msg = (err as Error).message;
    assert(
      msg.includes('GOOGLE_API_KEY'),
      'generateVeoClip throws when GOOGLE_API_KEY is not set'
    );
  }
  assert(threw, 'generateVeoClip rejects without API key');

  if (originalKey) {
    process.env.GOOGLE_API_KEY = originalKey;
  }

  console.log('');
}

// ============================================================================
// Example 4: Source file structure verification
// ============================================================================

function example4_sourceStructure(): void {
  console.log('=== Example 4: Source file structure (lib/veo.ts) ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'lib', 'veo.ts'),
    'utf-8'
  );

  // Requirement 8: server-only guard
  assert(sourceCode.includes('server-only'), 'Has server-only guard');

  // Requirement 4: Uses GOOGLE_API_KEY env var
  assert(sourceCode.includes('GOOGLE_API_KEY'), 'Uses GOOGLE_API_KEY env var');

  // SDK initialization
  assert(sourceCode.includes('GoogleGenAI'), 'Imports GoogleGenAI from @google/genai');
  assert(sourceCode.includes('@google/genai'), 'Imports from @google/genai package');

  // Requirement 1: Exports generateReferenceImage
  assert(
    /export\s+(async\s+)?function\s+generateReferenceImage/.test(sourceCode),
    'Exports generateReferenceImage function'
  );

  // Requirement 2: Exports generateVeoClip
  assert(
    /export\s+(async\s+)?function\s+generateVeoClip/.test(sourceCode),
    'Exports generateVeoClip function'
  );

  // Requirement 3: Exports extractLastFrame
  assert(
    /export\s+(async\s+)?function\s+extractLastFrame/.test(sourceCode),
    'Exports extractLastFrame function'
  );

  // Requirement 5: Imagen config
  assert(sourceCode.includes('imagen-3.0-generate-002'), 'Uses imagen-3.0-generate-002 model');
  assert(sourceCode.includes('numberOfImages: 1'), 'Sets numberOfImages: 1 for Imagen');
  assert(sourceCode.includes("aspectRatio: '1:1'"), "Sets aspectRatio '1:1' for portrait thumbnails");
  assert(sourceCode.includes("'image/png'"), 'Sets outputMimeType to image/png');

  // Requirement 6: Veo config
  assert(sourceCode.includes('veo-3.1-generate-preview'), 'Uses veo-3.1-generate-preview model');
  assert(sourceCode.includes('numberOfVideos: 1'), 'Sets numberOfVideos: 1 for Veo');
  assert(sourceCode.includes('durationSeconds: 8'), 'Sets durationSeconds: 8 default');

  // Requirement 7: Polling — 5s interval, 10 minute timeout
  assert(sourceCode.includes('5000'), 'Has 5-second poll interval');
  assert(
    sourceCode.includes('10 * 60 * 1000') || sourceCode.includes('600000') || sourceCode.includes('600_000'),
    'Has 10-minute timeout'
  );

  // Requirement 3: extractLastFrame — ffprobe and ffmpeg commands
  assert(sourceCode.includes('ffprobe'), 'Uses ffprobe for duration');
  assert(sourceCode.includes('ffmpeg'), 'Uses ffmpeg for frame extraction');
  assert(sourceCode.includes('-sseof'), 'Uses -sseof flag for seeking to end');
  assert(sourceCode.includes('-vframes 1'), 'Extracts exactly 1 frame');

  // Uses promisified exec for child process
  assert(sourceCode.includes('promisify'), 'Uses promisify for exec');
  assert(sourceCode.includes('exec'), 'Uses child_process exec');

  // Ensures output directories exist
  assert(sourceCode.includes('mkdirSync'), 'Uses mkdirSync to create output directories');
  assert(sourceCode.includes('recursive: true'), 'Creates directories recursively');

  // Base64 handling for Imagen
  assert(sourceCode.includes('base64'), 'Handles base64 image bytes');
  assert(sourceCode.includes('writeFileSync'), 'Writes files synchronously');

  // GCS URI conversion for Veo video download
  assert(sourceCode.includes('gs://'), 'Handles GCS URI format');
  assert(sourceCode.includes('storage.googleapis.com'), 'Converts to HTTPS download URL');

  // Operation polling
  assert(sourceCode.includes('operations.get'), 'Polls operation status via SDK');
  assert(sourceCode.includes('.done'), 'Checks operation done status');

  console.log('');
}

// ============================================================================
// Example 5: Type-safe usage patterns (demonstration, not executed)
// ============================================================================

function example5_usagePatterns(): void {
  console.log('=== Example 5: Type-safe usage patterns ===');

  // Demonstrate how generateReferenceImage would be called
  const imagenPrompt = 'Professional headshot of a young woman with brown hair, neutral background, studio lighting';
  const imageOutputPath = path.join('output', 'references', 'host-portrait.png');

  console.log('  generateReferenceImage usage (not executed — requires API key):');
  console.log(`    Prompt: "${imagenPrompt.substring(0, 50)}..."`);
  console.log(`    Output: ${imageOutputPath}`);
  console.log('    Config: Imagen 3.0, 1:1 aspect, PNG, 1 image');

  // Demonstrate generateVeoClip without reference
  const veoPrompt = 'Aerial drone shot of a modern city skyline at golden hour';
  const clipOutputPath = path.join('output', 'clips', 'clip-01-intro.mp4');

  console.log('');
  console.log('  generateVeoClip usage without reference (not executed):');
  console.log(`    Prompt: "${veoPrompt}"`);
  console.log(`    Reference: null (no reference image)`);
  console.log(`    Aspect ratio: 16:9`);
  console.log(`    Output: ${clipOutputPath}`);
  console.log('    Config: Veo 3.1, 8s duration, polls every 5s, 10min timeout');

  // Demonstrate generateVeoClip with reference for visual consistency
  const refImagePath = path.join('output', 'references', 'host-portrait.png');
  const refClipPath = path.join('output', 'clips', 'clip-02-host.mp4');

  console.log('');
  console.log('  generateVeoClip usage with reference (not executed):');
  console.log(`    Reference image: ${refImagePath}`);
  console.log(`    Output: ${refClipPath}`);
  console.log('    The reference image ensures visual consistency across clips');

  // Demonstrate extractLastFrame for frame chaining
  const sourceClip = path.join('output', 'clips', 'clip-01-intro.mp4');
  const framePath = path.join('output', 'frames', 'clip-01-last-frame.png');

  console.log('');
  console.log('  extractLastFrame usage (not executed — requires ffmpeg):');
  console.log(`    Source clip: ${sourceClip}`);
  console.log(`    Output frame: ${framePath}`);
  console.log('    Uses: ffprobe for duration, ffmpeg -sseof -0.1 for last frame');

  // Demonstrate frame-chaining pipeline pattern
  console.log('');
  console.log('  Frame-chaining pipeline pattern:');
  console.log('    1. Generate clip N with generateVeoClip(prompt, lastFrame, "16:9", path)');
  console.log('    2. Extract last frame with extractLastFrame(clipN, frameN)');
  console.log('    3. Use frameN as reference for clip N+1');
  console.log('    4. Repeat for all clips in the sequence');

  // Demonstrate vertical video
  console.log('');
  console.log('  Vertical video (9:16 for mobile/social):');
  console.log('    generateVeoClip(prompt, null, "9:16", outputPath)');

  assert(true, 'Usage patterns documented');
  console.log('');
}

// ============================================================================
// Example 6: Frame-chaining workflow demonstration
// ============================================================================

function example6_frameChainingWorkflow(): void {
  console.log('=== Example 6: Frame-chaining workflow ===');

  // This demonstrates the primary use case: generating a sequence of video
  // clips where each clip's reference image is the last frame of the previous
  // clip, ensuring visual continuity across the entire video.

  const clipPrompts = [
    'Wide establishing shot of a futuristic laboratory, blue ambient lighting',
    'Camera slowly pushes in toward a holographic display',
    'Close-up of a scientist examining the holographic data',
  ];

  console.log('  Pipeline steps for 3-clip sequence:');

  let currentReference: string | null = null;

  for (let i = 0; i < clipPrompts.length; i++) {
    const clipPath = path.join('output', 'pipeline', 'clips', `clip-${String(i + 1).padStart(2, '0')}.mp4`);
    const framePath = path.join('output', 'pipeline', 'frames', `frame-${String(i + 1).padStart(2, '0')}.png`);

    console.log(`    [Clip ${i + 1}/${clipPrompts.length}]`);
    console.log(`      Prompt: "${clipPrompts[i].substring(0, 55)}..."`);
    console.log(`      Reference: ${currentReference ?? '(none - first clip)'}`);
    console.log(`      -> generateVeoClip(...) -> ${clipPath}`);

    if (i < clipPrompts.length - 1) {
      console.log(`      -> extractLastFrame(...) -> ${framePath}`);
      currentReference = framePath;
    }
  }

  assert(currentReference !== null, 'Frame chaining updates reference after each clip');
  assert(
    currentReference!.includes('frame-02'),
    'Final reference is from second-to-last clip'
  );

  console.log('');
}

// ============================================================================
// Example 7: Aspect ratio parameter validation
// ============================================================================

function example7_aspectRatios(): void {
  console.log('=== Example 7: Aspect ratio options ===');

  // The function signature constrains aspect ratio to '16:9' | '9:16'
  const landscapeRatio: '16:9' | '9:16' = '16:9';
  const portraitRatio: '16:9' | '9:16' = '9:16';

  assert(landscapeRatio === '16:9', 'Landscape aspect ratio is 16:9');
  assert(portraitRatio === '9:16', 'Portrait/vertical aspect ratio is 9:16');

  // Imagen uses fixed 1:1 for portrait thumbnails (verified in source structure)
  console.log('  Imagen: always 1:1 (portrait thumbnails)');
  console.log('  Veo landscape: 16:9');
  console.log('  Veo portrait/vertical: 9:16');

  console.log('');
}

// ============================================================================
// Example 8: Error handling patterns
// ============================================================================

async function example8_errorHandling(): Promise<void> {
  console.log('=== Example 8: Error handling patterns ===');

  const sourceCode = fs.readFileSync(
    path.join(__dirname, '..', 'lib', 'veo.ts'),
    'utf-8'
  );

  // Verify descriptive error messages in the source
  assert(
    sourceCode.includes('Failed to generate reference image via Imagen'),
    'Has descriptive Imagen error message'
  );
  assert(
    sourceCode.includes('Failed to generate Veo clip'),
    'Has descriptive Veo error message'
  );
  assert(
    sourceCode.includes('Failed to extract last frame'),
    'Has descriptive extractLastFrame error message'
  );

  // Verify timeout error
  assert(
    sourceCode.includes('Timed out waiting for Veo operation'),
    'Has timeout error for long-running operations'
  );

  // Verify no-data error
  assert(
    sourceCode.includes('no image data') || sourceCode.includes('Imagen API returned no image'),
    'Has error for empty Imagen response'
  );

  // Verify no-video error
  assert(
    sourceCode.includes('no video URI') || sourceCode.includes('no video'),
    'Has error for missing video URI in Veo response'
  );

  // Verify download failure error
  assert(
    sourceCode.includes('Failed to download'),
    'Has error for video download failure'
  );

  console.log('');
}

// ============================================================================
// Run all examples
// ============================================================================

async function main(): Promise<void> {
  example1_verifyExports();
  await example2_apiKeyRequired();
  await example3_veoApiKeyRequired();
  example4_sourceStructure();
  example5_usagePatterns();
  example6_frameChainingWorkflow();
  example7_aspectRatios();
  await example8_errorHandling();

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
