import { NextRequest } from "next/server";
import fs from "fs";
import path from "path";

import { getJob } from "@/lib/jobs";
import { loadProject } from "@/lib/project";
import { createSseStream } from "@/lib/sse";
import { getProjectDir } from "@/lib/projects";

export const dynamic = "force-dynamic";

/**
 * GET /api/pipeline/render/stream?jobId=...
 *
 * Server-Sent Events endpoint for real-time render progress.
 * Polls the job status and section output files, emitting:
 *   - { type: 'section-progress', sectionId, percent } when a section file appears
 *   - { type: 'render-complete' } when the job completes
 *   - { type: 'render-error', message } when the job fails
 */
export async function GET(request: NextRequest): Promise<Response> {
  const jobId = request.nextUrl.searchParams.get("jobId");

  if (!jobId) {
    return new Response("Missing jobId parameter", { status: 400 });
  }

  let intervalId: ReturnType<typeof setInterval> | null = null;
  const reportedComplete = new Set<string>();

  const { stream, send, done, error } = createSseStream(() => {
    if (intervalId) clearInterval(intervalId);
  });

  const poll = () => {
    try {
      const sectionsDir = path.join(getProjectDir(), "outputs", "sections");
      const job = getJob(jobId);

      if (!job) {
        error("Job not found");
        if (intervalId) clearInterval(intervalId);
        return;
      }

      // Determine which sections this job is rendering
      const project = loadProject();
      const allSectionIds = project.sections.map((s) => s.id);
      const sectionsToRender: string[] = Array.isArray(job.params.sections)
        ? (job.params.sections as string[])
        : allSectionIds;

      // Emit section-progress 100% as output files appear
      for (const sectionId of sectionsToRender) {
        if (reportedComplete.has(sectionId)) continue;
        const outputPath = path.join(sectionsDir, `${sectionId}.mp4`);
        if (fs.existsSync(outputPath)) {
          send({ type: "section-progress", sectionId, percent: 100 });
          reportedComplete.add(sectionId);
        }
      }

      // Check terminal job status
      if (job.status === "done") {
        send({ type: "render-complete" });
        done();
        if (intervalId) clearInterval(intervalId);
      } else if (job.status === "error") {
        send({ type: "render-error", message: job.error ?? "Render failed" });
        error(job.error ?? "Render failed");
        if (intervalId) clearInterval(intervalId);
      }
    } catch (err) {
      console.error("Render stream poll error:", err);
    }
  };

  intervalId = setInterval(poll, 500);
  poll();

  request.signal.addEventListener("abort", () => {
    if (intervalId) clearInterval(intervalId);
  });

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}
