try { require('server-only'); } catch { /* running outside Next.js bundler */ }

import fs from "fs";
import os from "os";
import path from "path";
import { promisify } from "util";
import { exec, spawn } from "child_process";
// @remotion/renderer is used in spawned child scripts (see renderSection / renderStill)
// and must NOT be imported directly here — it crashes inside the Next.js server.
import type { RenderProgress } from "./types";
import {
  getAppDir,
  getAppNodeModulesDir,
  getAppRemotionDir,
} from "./projects";

const execAsync = promisify(exec);

/**
 * Resolve the Remotion bundle path.
 * Priority:
 * 1) REMOTION_BUNDLE_PATH env var (unless it points at a stale remotion/build/)
 * 2) remotion/build/ when it exists and is not older than remotion/src/
 * 3) Bundle remotion/src/index.ts into remotion/build on demand
 */
const getLatestMtimeMs = (entryPath: string): number => {
  if (!fs.existsSync(entryPath)) {
    return 0;
  }

  const stat = fs.statSync(entryPath);
  let latest = stat.mtimeMs;

  if (!stat.isDirectory()) {
    return latest;
  }

  for (const entry of fs.readdirSync(entryPath, { withFileTypes: true })) {
    latest = Math.max(
      latest,
      getLatestMtimeMs(path.join(entryPath, entry.name))
    );
  }

  return latest;
};

const getRemotionBuildDir = (): string => path.join(getAppRemotionDir(), "build");

const getRemotionSourceDir = (): string => path.join(getAppRemotionDir(), "src");

const resolveBundleDir = (candidatePath: string): string =>
  candidatePath.endsWith(".html") ? path.dirname(candidatePath) : candidatePath;

const isRemotionBuildDir = (candidateDir: string): boolean =>
  path.resolve(candidateDir) === path.resolve(getRemotionBuildDir());

const shouldPreferSourceOverBuild = (bundleDir: string): boolean => {
  return getLatestMtimeMs(getRemotionSourceDir()) > getLatestMtimeMs(bundleDir);
};

const getBundleCommand = (): string => {
  const remotionCli = path.join(
    getAppRemotionDir(),
    "node_modules",
    ".bin",
    "remotion"
  );
  return `"${remotionCli}" bundle "src/index.ts" --out "build"`;
};

let activeBuildRefresh:
  | { sourceVersion: number; promise: Promise<string> }
  | null = null;

const ensureFreshBuildDir = async (): Promise<string> => {
  const buildDir = getRemotionBuildDir();
  const buildIndexHtml = path.join(buildDir, "index.html");
  const sourceVersion = getLatestMtimeMs(getRemotionSourceDir());
  const buildIsFresh =
    fs.existsSync(buildIndexHtml) && !shouldPreferSourceOverBuild(buildDir);

  if (buildIsFresh) {
    return buildDir;
  }

  if (
    activeBuildRefresh &&
    activeBuildRefresh.sourceVersion === sourceVersion
  ) {
    return activeBuildRefresh.promise;
  }

  const promise = execAsync(getBundleCommand(), {
    cwd: getAppRemotionDir(),
    env: {
      ...process.env,
      NODE_PATH: [getAppNodeModulesDir(), process.env.NODE_PATH]
        .filter(Boolean)
        .join(path.delimiter),
    },
  }).then(() => buildDir);

  activeBuildRefresh = {
    sourceVersion,
    promise,
  };

  try {
    return await promise;
  } finally {
    if (activeBuildRefresh?.promise === promise) {
      activeBuildRefresh = null;
    }
  }
};

const getServeUrl = async (): Promise<string> => {
  const appDir = getAppDir();
  const envPath = process.env.REMOTION_BUNDLE_PATH;
  if (envPath) {
    // Resolve relative paths to absolute so Remotion can locate the bundle
    const resolvedEnvPath = path.isAbsolute(envPath)
      ? envPath
      : path.join(appDir, envPath);
    const bundleDir = resolveBundleDir(resolvedEnvPath);

    if (isRemotionBuildDir(bundleDir)) {
      return ensureFreshBuildDir();
    }

    return bundleDir;
  }

  // Auto-detect pre-compiled bundle: check for index.html in remotion/build/
  const buildDir = getRemotionBuildDir();
  const buildIndexHtml = path.join(buildDir, "index.html");
  if (fs.existsSync(buildIndexHtml)) {
    if (shouldPreferSourceOverBuild(buildDir)) {
      return ensureFreshBuildDir();
    }
    return buildDir;
  }

  return ensureFreshBuildDir();
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

  const serveUrl = await getServeUrl();

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
    await new Promise<void>((resolve, reject) => {
      const child = spawn("node", [scriptPath], {
        stdio: ["ignore", "pipe", "pipe"],
        cwd: getAppDir(),
        env: {
          ...process.env,
          NODE_PATH: getAppNodeModulesDir(),
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

  const serveUrl = await getServeUrl();

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
    await new Promise<void>((resolve, reject) => {
      const child = spawn("node", [scriptPath], {
        stdio: ["ignore", "ignore", "pipe"],
        cwd: getAppDir(),
        env: {
          ...process.env,
          NODE_PATH: getAppNodeModulesDir(),
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
