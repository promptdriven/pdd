import { NextRequest } from "next/server";

/**
 * GET /api/pipeline/audit/stream
 *
 * Server-Sent Events endpoint for real-time audit progress updates.
 * The audit/run POST actually drives the SSE events via the job system;
 * this endpoint provides a persistent connection for the client to listen on.
 * When no audit is actively running, it sends a heartbeat to keep the connection alive.
 */
export async function GET(_request: NextRequest) {
  const encoder = new TextEncoder();
  const stream = new ReadableStream({
    start(controller) {
      // Send an initial connected event
      controller.enqueue(
        encoder.encode(`data: ${JSON.stringify({ type: "connected" })}\n\n`)
      );

      // Keep alive with heartbeat every 15 seconds
      const interval = setInterval(() => {
        try {
          controller.enqueue(
            encoder.encode(`data: ${JSON.stringify({ type: "heartbeat" })}\n\n`)
          );
        } catch {
          clearInterval(interval);
        }
      }, 15000);

      // Clean up when the client disconnects
      _request.signal.addEventListener("abort", () => {
        clearInterval(interval);
        try {
          controller.close();
        } catch {
          // Already closed
        }
      });
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
