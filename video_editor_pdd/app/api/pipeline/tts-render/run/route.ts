import { NextRequest } from "next/server";
import { spawn } from "child_process";
import fs from "fs";
import path from "path";

import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";
import { parseSegmentsFromScript, getWavDuration } from "@/lib/tts-segments";
import type { SseSend } from "@/lib/types";
import { getAppScriptsDir, getProjectDir } from "@/lib/projects";

function pruneOrphanSegmentAudio(currentSegmentIds: string[]): void {
  if (currentSegmentIds.length === 0) {
    return;
  }

  const outputDir = path.join(getProjectDir(), "outputs", "tts");
  if (!fs.existsSync(outputDir)) {
    return;
  }

  const currentSet = new Set(currentSegmentIds);
  const wavFiles = fs
    .readdirSync(outputDir)
    .filter((file) => file.endsWith(".wav"));

  for (const wavFile of wavFiles) {
    const segmentId = wavFile.replace(/\.wav$/, "");
    if (currentSet.has(segmentId)) {
      continue;
    }

    try {
      fs.unlinkSync(path.join(outputDir, wavFile));
    } catch {
      // Ignore cleanup failures so rerender can continue.
    }
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
    path.join(getAppScriptsDir(), "render_tts.py"),
    ...(segments ?? []).flatMap((s) => ["--segment", s]),
  ];

  const proc = spawn("python3", args, {
    cwd: getProjectDir(),
    env: {
      ...process.env,
      // Prefer Qwen when it works, but allow the script to fall back to Edge TTS
      // so downstream audio-sync still receives real WAV files in local dev/test envs.
      RENDER_TTS_ALLOW_EDGE_FALLBACK:
        process.env.RENDER_TTS_ALLOW_EDGE_FALLBACK ?? "1",
    },
  });

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

    if (!segments || segments.length === 0) {
      pruneOrphanSegmentAudio(parseSegmentsFromScript().map((segment) => segment.id));
    }

    const success = await executeTtsRender(segments, send, onLog);

    // Emit per-segment statuses
    const segIds =
      segments && segments.length > 0
        ? segments
        : parseSegmentsFromScript().map((s) => s.id);

    for (const id of segIds) {
      const filePath = path.join(getProjectDir(), "outputs", "tts", `${id}.wav`);
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
 * Spawns render_tts.py via the pipeline job system (updates pipeline_status).
 */
export async function POST(request: NextRequest): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const segments =
    Array.isArray(body?.segments) && body.segments.length > 0
      ? (body.segments as string[])
      : undefined;

  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage(
        "tts-render",
        { segments },
        send
      );
      send({ type: "complete", jobId });
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
