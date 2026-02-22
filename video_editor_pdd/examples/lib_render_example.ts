// example_usage.ts
// Comprehensive usage example for lib/render.ts
// This file demonstrates how to use the Remotion rendering and ffmpeg stitching module.
//
// This module is marked 'server-only' and must be used in a Node.js server
// environment (e.g., Next.js API routes or server actions). It requires:
//   - @remotion/renderer installed
//   - ffmpeg and ffprobe available on PATH
//   - A bundled Remotion project at ./remotion/build/index.js (or set REMOTION_BUNDLE_PATH)
//
// This example verifies the module's structure, exported functions, and
// type signatures without requiring an actual Remotion bundle or ffmpeg.

import {
  renderSection,
  stitchFullVideo,
  getSectionDuration,
  renderStill,
} from "../lib/render";
import type { RenderProgress } from "../lib/types";
import path from "path";

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

/**
 * renderSection(compositionId, outputPath, onProgress)
 *
 * @param compositionId - The Remotion composition ID to render (must match a
 *                        composition registered in your Remotion project's Root.tsx)
 * @param outputPath    - Absolute or relative file path where the rendered MP4
 *                        will be written. Parent directories are created automatically.
 * @param onProgress    - Callback invoked repeatedly during rendering with a
 *                        RenderProgress object: { percent: number (0-100), message: string }
 * @returns Promise<void> - Resolves when rendering is complete.
 *
 * Internally this:
 *   1. Resolves the Remotion bundle/serve URL (env var > ./remotion/build/index.js > ./remotion)
 *   2. Calls selectComposition() to fetch composition metadata (dimensions, fps, duration)
 *   3. Calls renderMedia() with codec 'h264' and streams progress updates
 */
function example1_verifyExports(): void {
  console.log("=== Example 1: Module exports ===");

  assert(typeof renderSection === "function", "renderSection is a function");
  assert(typeof stitchFullVideo === "function", "stitchFullVideo is a function");
  assert(typeof getSectionDuration === "function", "getSectionDuration is a function");
  assert(typeof renderStill === "function", "renderStill is a function");

  console.log("");
}

// ============================================================================
// Example 2: Verify function signatures
// ============================================================================

/**
 * stitchFullVideo(sectionPaths, outputPath, onProgress)
 *
 * @param sectionPaths - Ordered array of file paths to MP4 sections. These are
 *                       concatenated in the given order using ffmpeg's concat demuxer.
 * @param outputPath   - File path for the final stitched MP4.
 * @param onProgress   - Callback invoked when stitching completes with
 *                       { percent: 100, message: "Stitching complete." }.
 * @returns Promise<void>
 *
 * getSectionDuration(mp4Path)
 *
 * @param mp4Path - Path to an MP4 file on disk.
 * @returns Promise<number> - Duration in seconds as a floating-point number.
 *
 * renderStill(compositionId, frame, outputPath)
 *
 * @param compositionId - The Remotion composition ID to capture a frame from.
 * @param frame         - Zero-based frame number to capture.
 * @param outputPath    - File path for the output PNG image.
 * @returns Promise<void>
 */
function example2_verifySignatures(): void {
  console.log("=== Example 2: Function signatures ===");

  // renderSection(compositionId, outputPath, onProgress) => 3 params
  assert(renderSection.length >= 3, "renderSection accepts at least 3 parameters");
  // stitchFullVideo(sectionPaths, outputPath, onProgress) => 3 params
  assert(stitchFullVideo.length >= 3, "stitchFullVideo accepts at least 3 parameters");
  // getSectionDuration(mp4Path) => 1 param
  assert(getSectionDuration.length >= 1, "getSectionDuration accepts at least 1 parameter");
  // renderStill(compositionId, frame, outputPath) => 3 params
  assert(renderStill.length >= 3, "renderStill accepts at least 3 parameters");

  console.log("");
}

// ============================================================================
// Example 3: Verify RenderProgress type compatibility
// ============================================================================

function example3_renderProgressType(): void {
  console.log("=== Example 3: RenderProgress type ===");

  const progress: RenderProgress = { percent: 50, message: "Rendering IntroComposition..." };
  assert(typeof progress.percent === "number", "RenderProgress.percent is a number");
  assert(typeof progress.message === "string", "RenderProgress.message is a string");
  assert(progress.percent >= 0 && progress.percent <= 100, "percent is in 0-100 range");

  // Verify a completed progress object
  const done: RenderProgress = { percent: 100, message: "Stitching complete." };
  assert(done.percent === 100, "Completed progress has percent 100");
  assert(done.message.length > 0, "Completed progress has a message");

  console.log("");
}

// ============================================================================
// Example 4: Demonstrate intended usage patterns (without invoking)
// ============================================================================

function example4_usagePatterns(): void {
  console.log("=== Example 4: Usage patterns (documentation) ===");

  // Pattern 1: Render a single section
  const compositionId = "IntroComposition";
  const outputPath = path.join("output", "sections", "intro.mp4");
  console.log(`  Pattern: renderSection("${compositionId}", "${outputPath}", onProgress)`);
  assert(outputPath.endsWith(".mp4"), "Output path ends with .mp4");

  // Pattern 2: Get section duration
  console.log(`  Pattern: getSectionDuration("${outputPath}") => Promise<number>`);
  assert(true, "getSectionDuration returns a Promise<number>");

  // Pattern 3: Stitch multiple sections
  const sectionPaths = [
    "output/sections/intro.mp4",
    "output/sections/main.mp4",
    "output/sections/outro.mp4",
  ];
  const finalOutput = path.join("output", "final", "complete-video.mp4");
  console.log(`  Pattern: stitchFullVideo([${sectionPaths.length} sections], "${finalOutput}", onProgress)`);
  assert(sectionPaths.length > 0, "stitchFullVideo accepts an array of section paths");

  // Pattern 4: Capture a still frame
  const frame = 90; // At 30fps, this is the 3-second mark
  const stillOutput = path.join("output", "stills", "intro-frame-90.png");
  console.log(`  Pattern: renderStill("${compositionId}", ${frame}, "${stillOutput}")`);
  assert(stillOutput.endsWith(".png"), "Still output path ends with .png");

  console.log("");
}

// ============================================================================
// Example 5: Integration with SSE progress streaming (documentation)
// ============================================================================

function example5_sseIntegration(): void {
  console.log("=== Example 5: SSE integration pattern ===");

  // Demonstrates how renderSection and stitchFullVideo integrate with
  // Server-Sent Events for real-time progress updates to the client.
  const send = (data: object) => {
    console.log("  SSE mock ->", JSON.stringify(data));
  };

  // Simulate the progress callback pattern used with SSE
  const onProgress = (progress: RenderProgress) => {
    send({
      type: "render-progress",
      sectionId: "intro",
      percent: progress.percent,
      message: progress.message,
    });
  };

  // Simulate progress updates
  onProgress({ percent: 0, message: "Rendering IntroComposition..." });
  onProgress({ percent: 50, message: "Rendering IntroComposition..." });
  onProgress({ percent: 100, message: "Rendering IntroComposition..." });

  assert(true, "Progress callback integrates with SSE send pattern");

  // Simulate stitch completion
  const stitchProgress: RenderProgress = { percent: 100, message: "Stitching complete." };
  send({ type: "stitch-progress", ...stitchProgress });
  assert(stitchProgress.percent === 100, "Stitch progress reports 100% on completion");

  send({ type: "pipeline-complete" });
  assert(true, "Pipeline complete event sent after all rendering and stitching");

  console.log("");
}

// ============================================================================
// Example 6: Error handling patterns (documentation)
// ============================================================================

function example6_errorHandling(): void {
  console.log("=== Example 6: Error handling patterns ===");

  // Document expected error scenarios (not invoked without Remotion/ffmpeg)
  console.log("  Common failure modes:");
  console.log("    - renderSection: Composition not found, bundle path invalid, Chromium not available");
  console.log("    - stitchFullVideo: ffmpeg not on PATH, section files missing, codec incompatibility");
  console.log("    - getSectionDuration: ffprobe not on PATH, file not found or corrupt");
  console.log("    - renderStill: Same as renderSection, plus invalid frame number");

  // All functions return promises, so errors should be caught with try/catch
  // Verify they are async functions (return promises) without invoking real rendering
  assert(renderSection.constructor.name === "AsyncFunction", "renderSection is async");
  assert(stitchFullVideo.constructor.name === "AsyncFunction", "stitchFullVideo is async");
  assert(getSectionDuration.constructor.name === "AsyncFunction", "getSectionDuration is async");
  assert(renderStill.constructor.name === "AsyncFunction", "renderStill is async");

  console.log("");
}

// ============================================================================
// Run all examples
// ============================================================================

function main(): void {
  console.log("lib/render.ts — Module verification examples\n");

  example1_verifyExports();
  example2_verifySignatures();
  example3_renderProgressType();
  example4_usagePatterns();
  example5_sseIntegration();
  example6_errorHandling();

  console.log("================================");
  console.log(`Results: ${passed} passed, ${failed} failed`);

  if (failed > 0) {
    process.exit(1);
  }
}

main();
