import { getJob } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";

export const dynamic = "force-dynamic";

/**
 * GET /api/jobs/[id]/stream
 * Server-Sent Events stream for real-time job logs and terminal status.
 */
export async function GET(
  _request: Request,
  { params }: { params: { id: string } }
): Promise<Response> {
  let intervalId: ReturnType<typeof setInterval> | null = null;
  let lastLineIndex = 0;
  let lastProgress = -1;
  let checkedOnce = false;

  const { stream, send, done, error } = createSseStream(() => {
    if (intervalId) clearInterval(intervalId);
  });

  const poll = () => {
    try {
      const job = getJob(params.id);

      if (!job) {
        if (!checkedOnce) {
          error("Job not found");
          if (intervalId) clearInterval(intervalId);
        }
        return;
      }

      checkedOnce = true;

      // 1. Send progress if it changed
      if (job.progress !== lastProgress) {
        send({ type: "progress", percent: job.progress });
        lastProgress = job.progress;
      }

      // 2. Send new logs
      const lines = job.logs ? job.logs.split("\n") : [];
      const lineCount =
        lines.length > 0 && lines[lines.length - 1] === ""
          ? lines.length - 1
          : lines.length;
      if (lineCount > lastLineIndex) {
        for (let i = lastLineIndex; i < lineCount; i++) {
          send({ type: "log", message: lines[i] });
        }
        lastLineIndex = lineCount;
      }

      // 3. Handle terminal status
      if (job.status === "done") {
        done();
        if (intervalId) clearInterval(intervalId);
      } else if (job.status === "error") {
        error(job.error ?? "Unknown error");
        if (intervalId) clearInterval(intervalId);
      }
    } catch (err) {
      console.error("SSE stream error:", err);
      error("Internal Server Error");
      if (intervalId) clearInterval(intervalId);
    }
  };

  // Poll immediately, then every 200ms
  intervalId = setInterval(poll, 200);
  poll();

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}