// lib/render.ts
try { require('server-only'); } catch {}

import path from 'path';
import os from 'os';
import fs from 'fs';
import { promisify } from 'util';
import { exec } from 'child_process';
import {
  renderMedia,
  renderStill as remotionRenderStill,
  selectComposition,
} from '@remotion/renderer';

import type { RenderProgress } from './types';

const execAsync = promisify(exec);

// Resolve Remotion bundle path (serve URL)
const REMOTION_BUNDLE_PATH =
  process.env.REMOTION_BUNDLE_PATH ?? path.join(process.cwd(), 'remotion');

/**
 * Ensure output directory exists.
 */
function ensureDir(filePath: string) {
  const dir = path.dirname(filePath);
  fs.mkdirSync(dir, { recursive: true });
}

/**
 * Render a Remotion composition section to MP4.
 */
export async function renderSection(
  compositionId: string,
  outputPath: string,
  onProgress: (p: RenderProgress) => void
): Promise<void> {
  ensureDir(outputPath);

  const composition = await selectComposition({
    serveUrl: REMOTION_BUNDLE_PATH,
    id: compositionId,
  });

  await renderMedia({
    composition,
    serveUrl: REMOTION_BUNDLE_PATH,
    codec: 'h264',
    outputLocation: outputPath,
    onProgress: ({ progress }) => {
      const percent = Math.round(progress * 100);
      onProgress({
        percent,
        message: `Rendering ${compositionId}...`,
      });
    },
  });
}

/**
 * Stitch MP4 sections into a full video using ffmpeg concat.
 */
export async function stitchFullVideo(
  sectionPaths: string[],
  outputPath: string,
  onProgress: (p: RenderProgress) => void
): Promise<void> {
  ensureDir(outputPath);

  const concatFile = path.join(os.tmpdir(), `concat-${Date.now()}.txt`);
  const concatContent = sectionPaths
    .map((p) => `file '${path.resolve(p)}'`)
    .join('\n');

  fs.writeFileSync(concatFile, concatContent);

  try {
    await execAsync(
      `ffmpeg -f concat -safe 0 -i "${concatFile}" -c copy "${outputPath}"`
    );

    onProgress({
      percent: 100,
      message: 'Stitching complete',
    });
  } finally {
    fs.unlinkSync(concatFile);
  }
}

/**
 * Get duration of an MP4 file in seconds using ffprobe.
 */
export async function getSectionDuration(mp4Path: string): Promise<number> {
  const { stdout } = await execAsync(
    `ffprobe -v error -show_entries format=duration -of default=noprint_wrappers=1:nokey=1 "${mp4Path}"`
  );

  return parseFloat(stdout.trim());
}

/**
 * Render a still PNG frame for audit screenshots.
 */
export async function renderStill(
  compositionId: string,
  frame: number,
  outputPath: string
): Promise<void> {
  ensureDir(outputPath);

  const composition = await selectComposition({
    serveUrl: REMOTION_BUNDLE_PATH,
    id: compositionId,
  });

  await remotionRenderStill({
    composition,
    serveUrl: REMOTION_BUNDLE_PATH,
    output: outputPath,
    frame,
  });
}