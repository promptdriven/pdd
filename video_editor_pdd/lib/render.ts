try { require('server-only'); } catch { /* running outside Next.js bundler */ }

import fs from "fs";
import os from "os";
import path from "path";
import { promisify } from "util";
import { exec } from "child_process";
import {
  renderMedia,
  renderStill as remotionRenderStill,
  selectComposition,
} from "@remotion/renderer";
import type { RenderProgress } from "./types";

const execAsync = promisify(exec);

/**
 * Resolve the Remotion bundle path.
 * Priority:
 * 1) REMOTION_BUNDLE_PATH env var
 * 2) remotion/build/index.js (if present)
 * 3) remotion (project root)
 */
const getServeUrl = (): string => {
  const envPath = process.env.REMOTION_BUNDLE_PATH;
  if (envPath) {
    // Resolve relative paths to absolute so Remotion can locate the bundle
    return path.isAbsolute(envPath)
      ? envPath
      : path.join(process.cwd(), envPath);
  }

  // Auto-detect pre-compiled bundle: check for index.html in remotion/build/
  const buildIndexHtml = path.join(
    process.cwd(),
    "remotion",
    "build",
    "index.html"
  );
  if (fs.existsSync(buildIndexHtml)) {
    return path.join(process.cwd(), "remotion", "build");
  }

  return path.join(process.cwd(), "remotion");
};

const ensureDir = async (filePath: string): Promise<void> => {
  const dir = path.dirname(filePath);
  await fs.promises.mkdir(dir, { recursive: true });
};

/**
 * Render a Remotion composition to MP4.
 */
export const renderSection = async (
  compositionId: string,
  outputPath: string,
  onProgress: (p: RenderProgress) => void
): Promise<void> => {
  await ensureDir(outputPath);

  const serveUrl = getServeUrl();
  const composition = await selectComposition({
    serveUrl,
    id: compositionId,
  });

  await renderMedia({
    composition,
    serveUrl,
    codec: "h264",
    outputLocation: outputPath,
    onProgress: ({ progress }) => {
      onProgress({
        percent: Math.round(progress * 100),
        message: `Rendering ${compositionId}...`,
      });
    },
  });
};

/**
 * Stitch MP4 sections into a single final output using ffmpeg concat.
 */
export const stitchFullVideo = async (
  sectionPaths: string[],
  outputPath: string,
  onProgress: (p: RenderProgress) => void
): Promise<void> => {
  await ensureDir(outputPath);

  const concatFile = path.join(os.tmpdir(), `concat-${Date.now()}.txt`);
  const concatContents = sectionPaths
    .map((p) => `file '${path.resolve(p).replace(/'/g, "'\\''")}'`)
    .join("\n");

  await fs.promises.writeFile(concatFile, concatContents, "utf-8");

  try {
    const cmd = `ffmpeg -f concat -safe 0 -i "${concatFile}" -c copy "${outputPath}"`;
    await execAsync(cmd);

    onProgress({
      percent: 100,
      message: "Stitching complete.",
    });
  } finally {
    await fs.promises.unlink(concatFile).catch(() => undefined);
  }
};

/**
 * Get duration (seconds) of a rendered MP4 using ffprobe.
 */
export const getSectionDuration = async (mp4Path: string): Promise<number> => {
  const cmd =
    `ffprobe -v error -show_entries format=duration ` +
    `-of default=noprint_wrappers=1:nokey=1 "${mp4Path}"`;

  const { stdout } = await execAsync(cmd);
  return parseFloat(stdout.trim());
};

/**
 * Render a single frame as PNG for audit screenshots.
 */
export const renderStill = async (
  compositionId: string,
  frame: number,
  outputPath: string
): Promise<void> => {
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
};