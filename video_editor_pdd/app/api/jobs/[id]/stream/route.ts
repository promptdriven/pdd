import { getJob } from "@/lib/jobs";

export const dynamic = "force-dynamic";

/**
 * GET /api/jobs/[id]/stream
 * Server-Sent Events stream for real-time job logs and terminal status.
 */
export async function GET(
  _request: Request,
  { params }: { params: { id: string } }
): Promise<Response> {
  const encoder = new TextEncoder();
  let intervalId: ReturnType<typeof setInterval> | null = null;

  const stream = new ReadableStream<Uint8Array>({ 
    start(controller) {
      let lastLineIndex = 0;
      let checkedOnce = false;
      let closed = false;

      const sendRaw = (payload: string) => {
        controller.enqueue(encoder.encode(payload));
      };

      const closeStream = () => {
        if (closed) return;
        closed = true;
        if (intervalId) clearInterval(intervalId);
        controller.close();
      };

      const sendLog = (message: string) => {
        sendRaw(`data: ${JSON.stringify({ type: "log", message })}\n\n`);
      };

      const sendDone = () => {
        sendRaw(`event: done\ndata: {}\n\n`);
      };

      const sendError = (message: string) => {
        sendRaw(`event: error\ndata: ${JSON.stringify({ message })}\n\n`);
      };

      const poll = () => {
        try {
          const job = getJob(params.id);

          if (!job) {
            if (!checkedOnce) {
              sendError("Job not found");
              closeStream();
            }
            return;
          }

          checkedOnce = true;

          const lines = job.logs ? job.logs.split("\n") : [];
          if (lines.length > lastLineIndex) {
            for (let i = lastLineIndex; i < lines.length; i++) {
              const line = lines[i];
              if (line) sendLog(line);
            }
            lastLineIndex = lines.length;
          }

          if (job.status === "done") {
            sendDone();
            closeStream();
          } else if (job.status === "error") {
            sendError(job.error ?? "Unknown error");
            closeStream();
          }
        } catch (err) {
          console.error("SSE stream error:", err);
          sendError("Internal Server Error");
          closeStream();
        }
      };

      // Poll immediately, then every 200ms
      poll();
      intervalId = setInterval(poll, 200);
    },

    cancel() {
      if (intervalId) clearInterval(intervalId);
    },
  });

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}