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

/**
 * Resolve the Remotion bundle serve URL.
 * Priority: REMOTION_BUNDLE_PATH env var → remotion/build directory → remotion directory.
 */
function getServeUrl(): string {
  const envPath = process.env.REMOTION_BUNDLE_PATH;
  if (envPath) return envPath;

  const buildIndex = path.join(process.cwd(), 'remotion', 'build', 'index.html');
  if (fs.existsSync(buildIndex)) {
    return path.join(process.cwd(), 'remotion', 'build');
  }

  return path.join(process.cwd(), 'remotion');
}

/**
 * Ensure output directory exists.
 */
async function ensureDir(filePath: string): Promise<void> {
  const dir = path.dirname(filePath);
  await fs.promises.mkdir(dir, { recursive: true });
}

/**
 * Escape single quotes in a file path for ffmpeg concat format.
 */
function escapeForConcat(p: string): string {
  return p.replace(/'/g, "'\\''");
}

/**
 * Render a Remotion composition section to MP4.
 */
export async function renderSection(
  compositionId: string,
  outputPath: string,
  onProgress: (p: RenderProgress) => void
): Promise<void> {
  await ensureDir(outputPath);

  const serveUrl = getServeUrl();
  const composition = await selectComposition({
    serveUrl,
    id: compositionId,
  });

  await renderMedia({
    composition,
    serveUrl,
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
  await ensureDir(outputPath);

  const concatFile = path.join(os.tmpdir(), `concat-${Date.now()}.txt`);
  const concatContent = sectionPaths
    .map((p) => `file '${escapeForConcat(path.resolve(p))}'`)
    .join('\n');

  await fs.promises.writeFile(concatFile, concatContent, 'utf-8');

  try {
    await execAsync(
      `ffmpeg -f concat -safe 0 -i "${concatFile}" -c copy "${outputPath}"`
    );

    onProgress({
      percent: 100,
      message: 'Stitching complete.',
    });
  } finally {
    await fs.promises.unlink(concatFile).catch(() => undefined);
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
  await ensureDir(outputPath);

  const serveUrl = getServeUrl();
  const composition = await selectComposition({
    serveUrl,
    id: compositionId,
  });

  await remotionRenderStill({
    composition,
    serveUrl,
    output: outputPath,
    frame,
  });
}
