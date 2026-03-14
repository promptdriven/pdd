import { NextRequest } from "next/server";
import path from "path";
import fs from "fs/promises";
import { spawn, execSync } from "child_process";

import { registerExecutor, startJobInBackground } from "@/lib/jobs";
import { renderSection, getSectionDuration } from "@/lib/render";
import { loadProject, saveProject } from "@/lib/project";
import {
  getAppRemotionDir,
  getAppRemotionPublicDir,
  getAppScriptsDir,
  getProjectDir,
} from "@/lib/projects";
import { buildSectionConstantsSource } from "@/lib/composition-timing";
import { resolveSectionCompositionIds } from "@/app/api/pipeline/_lib/composition-manifest";
import type { RenderProgress, SseSend } from "@/lib/types";

const VEO_MEDIA_EXTENSIONS = new Set([".mp4", ".webm", ".mov", ".m4v"]);

/**
 * Update project.json with duration and recalculated offsets
 */
async function updateProjectDurations(
  sectionId: string,
  durationSeconds: number
): Promise<void> {
  const config = loadProject();

  const target = config.sections.find((s) => s.id === sectionId);
  if (target) {
    target.durationSeconds = durationSeconds;
  }

  // Recalculate offsets based on order
  let offset = 0;
  for (const section of config.sections) {
    section.offsetSeconds = offset;
    offset += section.durationSeconds;
  }

  saveProject(config);
}

/**
 * Render sections in parallel batches
 */
async function renderSections(
  sectionIds: string[] | undefined,
  send: SseSend,
  onLog: (msg: string) => void
): Promise<void> {
  const projectDir = getProjectDir();
  const config = loadProject();
  const allSections = config.sections;

  const sectionsToRender = sectionIds?.length
    ? allSections.filter((s) => sectionIds.includes(s.id))
    : allSections;

  const maxParallel = config.render.maxParallelRenders || 1;

  await fs.mkdir(path.join(projectDir, "outputs", "sections"), { recursive: true });

  let updateChain: Promise<void> = Promise.resolve();

  for (let i = 0; i < sectionsToRender.length; i += maxParallel) {
    const batch = sectionsToRender.slice(i, i + maxParallel);

    await Promise.all(
      batch.map(async (section) => {
        const outputPath = path.join(
          projectDir,
          "outputs",
          "sections",
          `${section.id}.mp4`
        );

        onLog(`Rendering section "${section.id}"...`);

        await renderSection(
          section.compositionId,
          outputPath,
          (progress: RenderProgress) => {
            send({
              type: "section-progress",
              sectionId: section.id,
              percent: progress.percent,
            });
          }
        );

        const duration = await getSectionDuration(outputPath);

        updateChain = updateChain.then(() =>
          updateProjectDurations(section.id, duration)
        );
        await updateChain;

        onLog(
          `Section "${section.id}" rendered. Duration: ${duration.toFixed(2)}s`
        );
      })
    );
  }
}

async function syncVeoOutputsToRemotionPublic(onLog: (msg: string) => void): Promise<void> {
  const projectDir = getProjectDir();
  const sourceDir = path.join(projectDir, "outputs", "veo");
  const destDir = path.join(getAppRemotionPublicDir(), "veo");

  try {
    const entries = await fs.readdir(sourceDir, { withFileTypes: true });
    await fs.mkdir(destDir, { recursive: true });

    for (const entry of entries) {
      if (!entry.isFile()) {
        continue;
      }

      const ext = path.extname(entry.name).toLowerCase();
      if (!VEO_MEDIA_EXTENSIONS.has(ext)) {
        continue;
      }

      const src = path.join(sourceDir, entry.name);
      const dest = path.join(destDir, entry.name);
      await fs.copyFile(src, dest);
    }
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") {
      return;
    }

    onLog(`Warning: failed to sync Veo assets: ${err instanceof Error ? err.message : String(err)}`);
  }
}

async function refreshSectionTimelineArtifacts(
  sectionIds: string[] | undefined,
  onLog: (msg: string) => void
): Promise<void> {
  const projectDir = getProjectDir();
  const config = loadProject();
  const sectionsToRefresh = sectionIds?.length
    ? config.sections.filter((section) => sectionIds.includes(section.id))
    : config.sections;

  for (const section of sectionsToRefresh) {
    const componentIds = resolveSectionCompositionIds(section);

    if (componentIds.length === 0) {
      onLog(`Skipped section constants refresh for "${section.id}" because no compositions were discovered.`);
      continue;
    }

    const constantsDir = path.join(
      getAppRemotionDir(),
      "src",
      "remotion",
      section.id
    );
    const constantsPath = path.join(constantsDir, "constants.ts");
    const constantsSource = buildSectionConstantsSource(
      projectDir,
      section,
      componentIds
    );

    await fs.mkdir(constantsDir, { recursive: true });
    await fs.writeFile(constantsPath, constantsSource, "utf-8");
    onLog(`Regenerated section constants for "${section.id}".`);
  }
}

/**
 * Regenerate Root.tsx (to pick up Claude-generated flat section files)
 * and rebuild the Remotion bundle before rendering.
 */
async function rebuildBundle(
  sectionIds: string[] | undefined,
  onLog: (msg: string) => void
): Promise<void> {
  const projectDir = getProjectDir();
  onLog("Syncing staged Veo assets...");
  await syncVeoOutputsToRemotionPublic(onLog);

  onLog("Refreshing section timing artifacts...");
  await refreshSectionTimelineArtifacts(sectionIds, onLog);

  // Regenerate section wrappers and Root.tsx from project.json
  onLog("Regenerating Root.tsx...");
  await new Promise<void>((resolve, reject) => {
    const proc = spawn(
      "python3",
      [path.join(getAppScriptsDir(), "generate_section_compositions.py"), "--force"],
      { cwd: projectDir, stdio: ["ignore", "pipe", "pipe"] }
    );
    proc.stdout.on("data", (d) => onLog(d.toString()));
    proc.stderr.on("data", (d) => onLog(d.toString()));
    proc.on("close", (code) => {
      if (code === 0) resolve();
      else reject(new Error(`Wrapper generation failed (code ${code})`));
    });
  });

  const remotionDir = getAppRemotionDir();
  const buildDir = path.join(remotionDir, "build");
  const webpackCacheDir = path.join(
    remotionDir, "node_modules", ".cache", "webpack"
  );

  // Clear stale bundle and webpack cache to force fresh compilation
  onLog("Clearing stale bundle and webpack cache...");
  await fs.rm(buildDir, { recursive: true, force: true });
  await fs.rm(webpackCacheDir, { recursive: true, force: true });

  // Rebuild Remotion bundle so the renderer uses fresh compositions
  onLog("Rebuilding Remotion bundle...");
  execSync("npx remotion bundle src/index.ts --out build", {
    cwd: remotionDir,
    stdio: "pipe",
    timeout: 120_000,
  });
  onLog("Remotion bundle rebuilt.");
}

/**
 * Register the render executor for pipeline jobs
 */
registerExecutor("render", (params, send) => {
  return async (onLog) => {
    const sectionsParam = Array.isArray(params.sections)
      ? (params.sections as string[])
      : undefined;

    await rebuildBundle(sectionsParam, onLog);
    await renderSections(sectionsParam, send, onLog);
  };
});

/**
 * POST /api/pipeline/render/run
 * Starts the render job in the background and returns JSON { jobId } immediately.
 * Progress is streamed separately via GET /api/pipeline/render/stream?jobId=...
 */
export async function POST(request: NextRequest): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const sections = Array.isArray(body.sections)
    ? (body.sections as string[])
    : undefined;

  try {
    const jobId = startJobInBackground("render", { sections });
    return Response.json({ jobId });
  } catch (err) {
    return Response.json(
      { error: err instanceof Error ? err.message : "Unknown error" },
      { status: 500 }
    );
  }
}
