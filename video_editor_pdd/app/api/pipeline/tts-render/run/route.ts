import { NextRequest } from "next/server";
import { spawn } from "child_process";
import fs from "fs";
import path from "path";
import crypto from "crypto";

import { registerExecutor } from "@/lib/jobs";
import type { SseSend } from "@/lib/types";

/**
 * Create a basic SSE stream helper for Route Handlers.
 */
function createSseStream() {
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

  const done = () => {
    controller.close();
  };

  const error = (message: string) => {
    send({ type: "error", message });
    controller.close();
  };

  return { stream, send, done, error };
}

/**
 * Parse segment IDs and text from tts_script.md
 * Segment IDs are derived from heading markers.
 */
export function parseSegmentsFromScript(): { id: string; text?: string }[] {
  const scriptPath = path.join(process.cwd(), "narrative", "tts_script.md");
  if (!fs.existsSync(scriptPath)) return [];

  const content = fs.readFileSync(scriptPath, "utf-8");
  const lines = content.split(/\r?\n/);

  const segments: { id: string; text?: string }[] = [];
  let current: { id: string; lines: string[] } | null = null;

  for (const line of lines) {
    const heading = line.match(/^#{1,6}\s+(.+)$/);
    if (heading) {
      if (current) {
        const text = current.lines.join("\n").trim();
        segments.push({ id: current.id, text: text || undefined });
      }
      const headingText = heading[1].trim();
      const id = headingText.split(/\s+/)[0];
      current = { id, lines: [] };
    } else if (current) {
      current.lines.push(line);
    }
  }

  if (current) {
    const text = current.lines.join("\n").trim();
    segments.push({ id: current.id, text: text || undefined });
  }

  return segments;
}

/**
 * Extract duration from a WAV file (basic header parsing).
 */
export function getWavDuration(filePath: string): number | undefined {
  try {
    const buf = fs.readFileSync(filePath);
    if (buf.length < 44) return undefined;

    const numChannels = buf.readUInt16LE(22);
    const sampleRate = buf.readUInt32LE(24);
    const bitsPerSample = buf.readUInt16LE(34);
    const dataSize = buf.readUInt32LE(40);

    const bytesPerSample = bitsPerSample / 8;
    const duration = dataSize / (sampleRate * numChannels * bytesPerSample);

    return Math.round(duration * 1000) / 1000;
  } catch {
    return undefined;
  }
}

/**
 * Spawn render_tts.py and stream stdout/stderr via onLog.
 */
async function runRenderProcess(
  segments: string[] | undefined,
  onLog: (line: string) => void
): Promise<void> {
  const args = [
    path.join("scripts", "render_tts.py"),
    ...(segments ?? []).flatMap((s) => ["--segment", s]),
  ];

  const proc = spawn("python3", args, { cwd: process.cwd() });

  const pipeLines = (stream: NodeJS.ReadableStream) => {
    let buffer = "";
    stream.on("data", (chunk) => {
      buffer += chunk.toString();
      const lines = buffer.split(/\r?\n/);
      buffer = lines.pop() ?? "";
      for (const line of lines) {
        if (line.trim().length > 0) onLog(line);
      }
    });
    stream.on("end", () => {
      if (buffer.trim().length > 0) onLog(buffer);
    });
  };

  pipeLines(proc.stdout);
  pipeLines(proc.stderr);

  await new Promise<void>((resolve, reject) => {
    proc.on("error", reject);
    proc.on("close", (code) => {
      if (code === 0) resolve();
      else reject(new Error(`render_tts.py exited with code ${code}`));
    });
  });
}

/**
 * Shared executor (also used for pipeline orchestration).
 */
async function executeTtsRender(
  segments: string[] | undefined,
  send: SseSend,
  onLog: (line: string) => void
): Promise<boolean> {
  try {
    await runRenderProcess(segments, onLog);
    return true;
  } catch (err) {
    const msg =
      err instanceof Error ? err.message : "Unknown render error";
    send({ type: "error", message: msg });
    return false;
  }
}

/**
 * Register executor for the pipeline job system.
 */
registerExecutor("tts-render", (params, send) => {
  return async (onLog) => {
    const segments = Array.isArray(params.segments)
      ? (params.segments as string[])
      : undefined;

    const success = await executeTtsRender(segments, send, onLog);

    // Emit per-segment statuses
    const segIds =
      segments && segments.length > 0
        ? segments
        : parseSegmentsFromScript().map((s) => s.id);

    for (const id of segIds) {
      const filePath = path.join(process.cwd(), "outputs", "tts", `${id}.wav`);
      const exists = fs.existsSync(filePath);
      const duration = exists ? getWavDuration(filePath) : undefined;
      send({
        type: "segment",
        segmentId: id,
        status: success && exists ? "done" : "error",
        duration,
      });
    }
  };
});

/**
 * POST /api/pipeline/tts-render/run
 * Spawns render_tts.py and streams SSE output.
 */
export async function POST(request: NextRequest): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const segments =
    Array.isArray(body?.segments) && body.segments.length > 0
      ? (body.segments as string[])
      : undefined;

  const { stream, send, done } = createSseStream();
  const jobId = crypto.randomUUID();

  // First SSE event must include jobId
  send({ jobId });

  // Run async without blocking response
  (async () => {
    const onLog = (line: string) => {
      send({ type: "log", message: line, jobId });
    };

    const success = await executeTtsRender(segments, send, onLog);

    const segIds =
      segments && segments.length > 0
        ? segments
        : parseSegmentsFromScript().map((s) => s.id);

    for (const id of segIds) {
      const filePath = path.join(process.cwd(), "outputs", "tts", `${id}.wav`);
      const exists = fs.existsSync(filePath);
      const duration = exists ? getWavDuration(filePath) : undefined;

      send({
        type: "segment",
        segmentId: id,
        status: success && exists ? "done" : "error",
        duration,
      });
    }

    done();
  })().catch((err) => {
    console.error("TTS render error:", err);
    send({
      type: "error",
      message: err instanceof Error ? err.message : "Unknown error",
    });
    done();
  });

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}
