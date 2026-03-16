import { NextRequest } from "next/server";
import path from "path";
import { spawn } from "child_process";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { loadProject } from "@/lib/project";
import type { SseSend } from "@/lib/types";
import { getAppRemotionPublicDir, getAppScriptsDir, getProjectDir } from "@/lib/projects";

/**
 * Simple SSE stream helper for Next.js Route Handlers.
 */
function createSseStream() {
  const encoder = new TextEncoder();
  let controller: ReadableStreamDefaultController<Uint8Array> | null = null;

  const stream = new ReadableStream<Uint8Array>({
    start(c) {
      controller = c;
    },
  });

  const send = (data: object) => {
    if (!controller) return;
    controller.enqueue(encoder.encode(`data: ${JSON.stringify(data)}\n\n`));
  };

  const done = () => {
    if (!controller) return;
    controller.close();
  };

  const error = (message: string) => {
    send({ type: "error", error: message });
    done();
  };

  return { stream, send, done, error };
}

/**
 * Register executor for the audio-sync pipeline stage.
 * This spawns sync_audio_pipeline.py and emits SSE section events.
 */
registerExecutor("audio-sync", (params, send: SseSend) => {
  return async (onLog) => {
    const project = loadProject();
    const allSectionGroups = project.audioSync?.sectionGroups ?? {};
    const requestedSections = Array.isArray(params.sections)
      ? params.sections.filter((sectionId): sectionId is string => typeof sectionId === "string")
      : [];
    const sectionGroups =
      requestedSections.length > 0
        ? Object.fromEntries(
            Object.entries(allSectionGroups).filter(([sectionId]) =>
              requestedSections.includes(sectionId)
            )
          )
        : allSectionGroups;

    onLog(`[audio-sync] Loaded sectionGroups: ${JSON.stringify(sectionGroups)}`);

    // Spawn the Python script
    const proc = spawn(
      "python3",
      [
        path.join(getAppScriptsDir(), "sync_audio_pipeline.py"),
        "--project-dir",
        getProjectDir(),
        "--remotion-public",
        getAppRemotionPublicDir(),
      ],
      {
        cwd: getProjectDir(),
        env: {
          ...process.env,
          SECTION_GROUPS: JSON.stringify(sectionGroups),
        },
      }
    );

    let stdoutBuffer = "";

    proc.stdout.on("data", (chunk: Buffer) => {
      stdoutBuffer += chunk.toString();

      let lineBreakIndex: number;
      while ((lineBreakIndex = stdoutBuffer.indexOf("\n")) !== -1) {
        const line = stdoutBuffer.slice(0, lineBreakIndex).trim();
        stdoutBuffer = stdoutBuffer.slice(lineBreakIndex + 1);

        if (!line) continue;

        // Try to parse JSON lines for SSE section events
        try {
          const parsed = JSON.parse(line);
          if (
            parsed &&
            parsed.type === "section" &&
            parsed.sectionId &&
            (parsed.status === "done" || parsed.status === "error")
          ) {
            send(parsed);
          } else {
            onLog(line);
          }
        } catch {
          // Non-JSON output, treat as log
          onLog(line);
        }
      }
    });

    proc.stderr.on("data", (chunk: Buffer) => {
      onLog(`[stderr] ${chunk.toString()}`);
    });

    await new Promise<void>((resolve, reject) => {
      proc.on("close", (code) => {
        if (code === 0) {
          resolve();
        } else {
          reject(new Error(`sync_audio_pipeline.py exited with code ${code}`));
        }
      });

      proc.on("error", (err) => {
        reject(err);
      });
    });
  };
});

/**
 * POST /api/pipeline/audio-sync/run
 * Streams audio-sync progress via SSE. Returns { jobId } event when complete.
 */
export async function POST(_request: NextRequest): Promise<Response> {
  const { stream, send, done, error } = createSseStream();
  const body = await _request.json().catch(() => ({}));
  const sections = Array.isArray(body?.sections)
    ? body.sections.filter((sectionId: unknown): sectionId is string => typeof sectionId === "string")
    : undefined;

  (async () => {
    try {
      const jobId = await runPipelineStage(
        "audio-sync",
        sections && sections.length > 0 ? { sections } : {},
        send
      );
      send({ type: "job", jobId });
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
