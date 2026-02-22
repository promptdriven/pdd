import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs/promises";
import { randomUUID } from "crypto";

import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { renderSection, getSectionDuration, stitchFullVideo } from "@/lib/render";
import { loadProject, saveProject } from "@/lib/project";
import type { RenderProgress, SseSend } from "@/lib/types";

/**
 * SSE stream helper (minimal, local implementation)
 */
function createSseStream(): {
  stream: ReadableStream<Uint8Array>;
  send: SseSend;
  done: () => void;
  error: (message: string) => void;
} {
  const encoder = new TextEncoder();
  let controller: ReadableStreamDefaultController<Uint8Array>;

  const stream = new ReadableStream<Uint8Array>({
    start(c) {
      controller = c;
    },
  });

  const send: SseSend = (data: object) => {
    const payload = `data: ${JSON.stringify(data)}\n\n`;
    controller.enqueue(encoder.encode(payload));
  };

  const done = () => controller.close();

  const error = (message: string) => {
    send({ type: "error", message });
    controller.close();
  };

  return { stream, send, done, error };
}

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
 * Starts rendering sections with SSE streaming.
 */
export async function POST_render(request: NextRequest): Promise<NextResponse> {
  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const body = await request.json().catch(() => ({}));
      const sections = Array.isArray(body.sections)
        ? (body.sections as string[])
        : undefined;

      const jobId = await runPipelineStage("render", { sections }, send);

      send({ jobId });
      done();
    } catch (err) {
      console.error("Render run failed:", err);
      error(err instanceof Error ? err.message : "Unknown error");
    }
  })();

  return new NextResponse(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}

/**
 * POST /api/pipeline/stitch/run
 */
export async function POST_stitch(_request: NextRequest): Promise<NextResponse> {
  try {
    const project = loadProject();
    const sectionPaths = project.sections.map((s) =>
      path.join("outputs", "sections", `${s.id}.mp4`)
    );
    const outputPath = path.join("outputs", "full_video.mp4");
    await fs.mkdir("outputs", { recursive: true });
    const jobId = randomUUID();
    await stitchFullVideo(sectionPaths, outputPath, () => {});
    return NextResponse.json({ jobId }, { status: 200 });
  } catch (err) {
    console.error("Stitch run failed:", err);
    return NextResponse.json({ error: "Internal Server Error" }, { status: 500 });
  }
}

/**
 * GET /api/pipeline/render/status
 */
export async function GET_status(_request: NextRequest): Promise<NextResponse> {
  try {
    const project = loadProject();
    const sectionStatuses = await Promise.all(
      project.sections.map(async (section) => {
        const outputPath = path.join("outputs", "sections", `${section.id}.mp4`);
        try {
          await fs.access(outputPath);
          const duration = await getSectionDuration(outputPath);
          return { sectionId: section.id, status: "done", duration };
        } catch {
          return { sectionId: section.id, status: "missing" };
        }
      })
    );
    const fullVideoPath = path.join("outputs", "full_video.mp4");
    let fullVideo: any = { exists: false };
    try {
      const stat = await fs.stat(fullVideoPath);
      fullVideo = { exists: true, path: fullVideoPath, size: stat.size };
      fullVideo.duration = await getSectionDuration(fullVideoPath);
    } catch {}
    return NextResponse.json({ sections: sectionStatuses, fullVideo }, { status: 200 });
  } catch (err) {
    return NextResponse.json({ error: "Internal Server Error" }, { status: 500 });
  }
}