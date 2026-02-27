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
 * Simple SSE stream helper
 */
function createSseStream() {
  const encoder = new TextEncoder();
  let controller: ReadableStreamDefaultController<Uint8Array> | null = null;

  const stream = new ReadableStream<Uint8Array>({
    start(c) {
      controller = c;
    },
  });

  const send = (data: object) => {
    if (!controller) return;
    controller.enqueue(encoder.encode(`data: ${JSON.stringify(data)}\n\n`));
  };

  const done = () => {
    if (!controller) return;
    try { controller.close(); } catch { /* already closed */ }
  };

  const error = (message: string) => {
    send({ type: "error", message });
    done();
  };

  return { stream, send, done, error };
}

/**
 * POST /api/pipeline/render/run
 * Streams render progress via SSE. Returns { jobId } event when complete.
 */
export async function POST(request: NextRequest): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const sections = Array.isArray(body.sections)
    ? (body.sections as string[])
    : undefined;

  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage("render", { sections }, send);
      send({ jobId });
      done();
    } catch (err) {
      error(err instanceof Error ? err.message : "Unknown error");
    }
  })();

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}

