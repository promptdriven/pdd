try { require('server-only'); } catch { /* running outside Next.js bundler */ }

import fs from "fs";
import os from "os";
import path from "path";
import { promisify } from "util";
import { exec, spawn } from "child_process";
// @remotion/renderer is used in spawned child scripts (see renderSection / renderStill)
// and must NOT be imported directly here — it crashes inside the Next.js server.
import type { RenderProgress } from "./types";
import { getProjectDir } from "./projects";

const execAsync = promisify(exec);

/**
 * Resolve the Remotion bundle path.
 * Priority:
 * 1) REMOTION_BUNDLE_PATH env var
 * 2) remotion/build/index.js (if present)
 * 3) remotion (project root)
 */
const getServeUrl = (): string => {
  const projectDir = getProjectDir();
  const envPath = process.env.REMOTION_BUNDLE_PATH;
  if (envPath) {
    // Resolve relative paths to absolute so Remotion can locate the bundle
    return path.isAbsolute(envPath)
      ? envPath
      : path.join(projectDir, envPath);
  }

  // Auto-detect pre-compiled bundle: check for index.html in remotion/build/
  const buildIndexHtml = path.join(
    projectDir,
    "remotion",
    "build",
    "index.html"
  );
  if (fs.existsSync(buildIndexHtml)) {
    return path.join(projectDir, "remotion", "build");
  }

  return path.join(projectDir, "remotion");
};

const ensureDir = async (filePath: string): Promise<void> => {
  const dir = path.dirname(filePath);
  await fs.promises.mkdir(dir, { recursive: true });
};

/**
 * Render a Remotion composition to MP4 in a standalone Node.js child process.
 *
 * Remotion's renderMedia() hangs when called inside the Next.js dev server
 * due to module resolution conflicts and event-loop contention. Spawning a
 * separate Node process avoids this entirely.
 *
 * The child process communicates progress via JSON lines on stdout.
 */
export const renderSection = async (
  compositionId: string,
  outputPath: string,
  onProgress: (p: RenderProgress) => void
): Promise<void> => {
  await ensureDir(outputPath);

  const serveUrl = getServeUrl();

  // Write a temporary .cjs script that performs the actual render
  const scriptPath = path.join(
    os.tmpdir(),
    `remotion-render-${compositionId}-${Date.now()}.cjs`
  );

  const script = `
const { selectComposition, renderMedia } = require('@remotion/renderer');
const path = require('path');

async function run() {
  const serveUrl = ${JSON.stringify(serveUrl)};
  const compositionId = ${JSON.stringify(compositionId)};
  const outputLocation = ${JSON.stringify(outputPath)};

  const composition = await selectComposition({ serveUrl, id: compositionId });

  await renderMedia({
    composition,
    serveUrl,
    codec: 'h264',
    outputLocation,
    onProgress: ({ progress }) => {
      const percent = Math.round(progress * 100);
      process.stdout.write(JSON.stringify({ percent, compositionId }) + '\\n');
    },
  });

  process.stdout.write(JSON.stringify({ percent: 100, compositionId, done: true }) + '\\n');
}

run().catch((err) => {
  process.stderr.write(err.message || String(err));
  process.exit(1);
});
`.trim();

  await fs.promises.writeFile(scriptPath, script, "utf-8");

  try {
    const projectDir = getProjectDir();
    await new Promise<void>((resolve, reject) => {
      const child = spawn("node", [scriptPath], {
        stdio: ["ignore", "pipe", "pipe"],
        cwd: projectDir,
        env: {
          ...process.env,
          NODE_PATH: path.join(projectDir, "node_modules"),
        },
      });

      let stderr = "";
      let buffer = "";

      child.stdout.on("data", (chunk: Buffer) => {
        buffer += chunk.toString();
        const lines = buffer.split("\n");
        buffer = lines.pop() ?? "";

        for (const line of lines) {
          if (!line.trim()) continue;
          try {
            const data = JSON.parse(line);
            onProgress({
              percent: data.percent ?? 0,
              message: `Rendering ${compositionId}...`,
            });
          } catch {
            // not JSON, ignore
          }
        }
      });

      child.stderr.on("data", (chunk: Buffer) => {
        stderr += chunk.toString();
      });

      child.on("error", reject);
      child.on("close", (code) => {
        if (code === 0) {
          resolve();
        } else {
          reject(
            new Error(
              `Render process for "${compositionId}" exited with code ${code}: ${stderr.trim()}`
            )
          );
        }
      });
    });
  } finally {
    await fs.promises.unlink(scriptPath).catch(() => undefined);
  }
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
    const cmd = `ffmpeg -y -f concat -safe 0 -i "${concatFile}" -c copy "${outputPath}"`;
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
 * Extract a single frame from a rendered video at a specific timestamp.
 */
export const extractFrameAtTime = async (
  videoPath: string,
  timeSeconds: number,
  outputPath: string
): Promise<void> => {
  await ensureDir(outputPath);

  const safeTimeSeconds = Math.max(0, timeSeconds);
  const cmd =
    `ffmpeg -y -ss ${safeTimeSeconds.toFixed(3)} -i "${videoPath}" ` +
    `-vframes 1 -q:v 2 "${outputPath}"`;

  await execAsync(cmd);
};

/**
 * Render a single frame as PNG for audit screenshots.
 *
 * Spawns a child process to avoid bufferUtil / module-resolution
 * conflicts inside the Next.js dev server (same approach as renderSection).
 */
export const renderStill = async (
  compositionId: string,
  frame: number,
  outputPath: string
): Promise<void> => {
  await ensureDir(outputPath);

  const serveUrl = getServeUrl();

  const scriptPath = path.join(
    os.tmpdir(),
    `remotion-still-${compositionId}-${Date.now()}.cjs`
  );

  const script = `
const { selectComposition, renderStill } = require('@remotion/renderer');

async function run() {
  const serveUrl = ${JSON.stringify(serveUrl)};
  const compositionId = ${JSON.stringify(compositionId)};
  const outputLocation = ${JSON.stringify(outputPath)};
  const frame = ${JSON.stringify(frame)};

  const composition = await selectComposition({ serveUrl, id: compositionId });
  await renderStill({ composition, serveUrl, output: outputLocation, frame });
}

run().catch((err) => {
  process.stderr.write(err.message || String(err));
  process.exit(1);
});
`.trim();

  await fs.promises.writeFile(scriptPath, script, "utf-8");

  try {
    const projectDir = getProjectDir();
    await new Promise<void>((resolve, reject) => {
      const child = spawn("node", [scriptPath], {
        stdio: ["ignore", "ignore", "pipe"],
        cwd: projectDir,
        env: {
          ...process.env,
          NODE_PATH: path.join(projectDir, "node_modules"),
        },
      });

      let stderr = "";

      child.stderr.on("data", (chunk: Buffer) => {
        stderr += chunk.toString();
      });

      child.on("error", reject);
      child.on("close", (code) => {
        if (code === 0) {
          resolve();
        } else {
          reject(
            new Error(
              `Still render for "${compositionId}" frame ${frame} exited with code ${code}: ${stderr.trim()}`
            )
          );
        }
      });
    });
  } finally {
    await fs.promises.unlink(scriptPath).catch(() => undefined);
  }
};
