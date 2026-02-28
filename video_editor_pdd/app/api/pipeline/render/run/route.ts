import { NextRequest } from "next/server";
import path from "path";
import fs from "fs/promises";

import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { renderSection, getSectionDuration } from "@/lib/render";
import { loadProject, saveProject } from "@/lib/project";
import type { RenderProgress, SseSend } from "@/lib/types";

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
  const config = loadProject();
  const allSections = config.sections;

  const sectionsToRender = sectionIds?.length
    ? allSections.filter((s) => sectionIds.includes(s.id))
    : allSections;

  const maxParallel = config.render.maxParallelRenders || 1;

  await fs.mkdir(path.join("outputs", "sections"), { recursive: true });

  let updateChain: Promise<void> = Promise.resolve();

  for (let i = 0; i < sectionsToRender.length; i += maxParallel) {
    const batch = sectionsToRender.slice(i, i + maxParallel);

    await Promise.all(
      batch.map(async (section) => {
        const outputPath = path.join(
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

/**
 * Register the render executor for pipeline jobs
 */
registerExecutor("render", (params, send) => {
  return async (onLog) => {
    const sectionsParam = Array.isArray(params.sections)
      ? (params.sections as string[])
      : undefined;

    await renderSections(sectionsParam, send, onLog);
  };
});

/**
 * POST /api/pipeline/render/run
 * Starts the render job and returns JSON { jobId }.
 * Progress is streamed separately via GET /api/pipeline/render/stream?jobId=...
 */
export async function POST(request: NextRequest): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const sections = Array.isArray(body.sections)
    ? (body.sections as string[])
    : undefined;

  try {
    const noop: SseSend = () => {};
    const jobId = await runPipelineStage("render", { sections }, noop);
    return Response.json({ jobId });
  } catch (err) {
    return Response.json(
      { error: err instanceof Error ? err.message : "Unknown error" },
      { status: 500 }
    );
  }
}

