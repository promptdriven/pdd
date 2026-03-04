/**
 * GET /api/pipeline/veo/stream
 *
 * SSE endpoint for streaming Veo clip generation progress events.
 * The Stage 7 component connects to this to receive real-time status updates.
 *
 * Subscribes to the clip event bus (lib/clip-events.ts) so that events
 * emitted by the Veo executor are forwarded to the frontend EventSource.
 */

import { onClipEvent } from "@/lib/clip-events";

export const runtime = "nodejs";

export async function GET(): Promise<Response> {
  const encoder = new TextEncoder();
  let cleanup: (() => void) | null = null;

  const stream = new ReadableStream({
    start(controller) {
      // Send initial connection event
      controller.enqueue(
        encoder.encode(`data: ${JSON.stringify({ type: "connected" })}\n\n`)
      );

      // Subscribe to clip events and forward them as SSE data
      const unsubscribe = onClipEvent((event) => {
        const payload = JSON.stringify({ type: "clip", ...event });
        try {
          controller.enqueue(encoder.encode(`data: ${payload}\n\n`));
        } catch {
          // Stream already closed
        }
      });

      // Heartbeat to keep connection alive
      const interval = setInterval(() => {
        try {
          controller.enqueue(encoder.encode(`: heartbeat\n\n`));
        } catch {
          clearInterval(interval);
        }
      }, 30_000);

      // Auto-close after 5 minutes
      const timeout = setTimeout(() => {
        clearInterval(interval);
        unsubscribe();
        try {
          controller.close();
        } catch {
          // already closed
        }
      }, 5 * 60 * 1000);

      // Store cleanup for cancel()
      cleanup = () => {
        clearInterval(interval);
        clearTimeout(timeout);
        unsubscribe();
      };
    },
    cancel() {
      cleanup?.();
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
