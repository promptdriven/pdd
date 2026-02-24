/**
 * GET /api/pipeline/veo/stream
 *
 * SSE endpoint for streaming Veo clip generation progress events.
 * The Stage 7 component connects to this to receive real-time status updates.
 * For now this returns an open SSE stream that sends a heartbeat every 30s.
 */

export const runtime = "nodejs";

export async function GET(): Promise<Response> {
  const stream = new TransformStream();
  const writer = stream.writable.getWriter();
  const encoder = new TextEncoder();

  // Send initial connection event
  writer.write(encoder.encode(`data: ${JSON.stringify({ type: "connected" })}\n\n`));

  // Heartbeat to keep connection alive; close after 5 minutes of inactivity
  const interval = setInterval(() => {
    writer.write(encoder.encode(`: heartbeat\n\n`)).catch(() => {
      clearInterval(interval);
    });
  }, 30_000);

  // Auto-close after 5 minutes
  setTimeout(() => {
    clearInterval(interval);
    writer.close().catch(() => {});
  }, 5 * 60 * 1000);

  return new Response(stream.readable, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}
