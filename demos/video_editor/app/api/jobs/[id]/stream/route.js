import { NextResponse } from 'next/server';
const { getJob, addSubscriber, removeSubscriber } = require('@/lib/jobs');

export async function GET(request, { params }) {
  const { id } = await params;
  const job = getJob(id);
  if (!job) {
    return NextResponse.json({ error: 'Job not found', code: 'JOB_NOT_FOUND' }, { status: 404 });
  }

  const encoder = new TextEncoder();
  let writerRef = null;

  const stream = new ReadableStream({
    start(controller) {
      const writer = {
        write(data) {
          controller.enqueue(encoder.encode(data));
        },
        close() {
          try { controller.close(); } catch { /* already closed */ }
        },
      };
      writerRef = writer;

      const result = addSubscriber(id, writer);
      if (result && (result.status === 'done' || result.status === 'error')) {
        // Terminal state — close after sending current state
        try { controller.close(); } catch { /* ignore */ }
      }
    },
    cancel() {
      if (writerRef) removeSubscriber(id, writerRef);
    },
  });

  return new Response(stream, {
    headers: {
      'Content-Type': 'text/event-stream',
      'Cache-Control': 'no-cache',
      'Connection': 'keep-alive',
    },
  });
}
