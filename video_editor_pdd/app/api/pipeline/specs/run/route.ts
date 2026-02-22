import { NextRequest } from "next/server";
import path from "path";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { runClaudeFix } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import type { SseSend } from "@/lib/types";

// ----------------------------------------------------------------------------
// SSE helper
// ----------------------------------------------------------------------------
function createSseStream() {
  const stream = new TransformStream();
  const writer = stream.writable.getWriter();
  const encoder = new TextEncoder();

  const send: SseSend = (data: object) => {
    writer.write(encoder.encode(`data: ${JSON.stringify(data)}\n\n`));
  };

  const done = () => {
    writer.close();
  };

  const error = (message: string) => {
    send({ type: "error", error: message });
    done();
  };

  return { stream: stream.readable, send, done, error };
}

// ----------------------------------------------------------------------------
// Register specs executor (runs Claude scoped to /specs)
// ----------------------------------------------------------------------------
registerExecutor("specs", (params, _send) => {
  return async (onLog) => {
    const cfg = loadProject();
    const allSectionIds = cfg.sections.map((s) => s.id);

    const sectionIds =
      Array.isArray(params.sections) && params.sections.length > 0
        ? (params.sections as string[])
        : allSectionIds;

    const files =
      Array.isArray(params.files) && params.files.length > 0
        ? (params.files as string[])
        : [];

    const prompt = `
You are generating visual spec markdown files for a video pipeline.

Instructions:
- Generate specs ONLY under the specs/ directory.
- Each section should have spec files under: specs/<sectionId>/.
- Use these visual type markers on the FIRST line if applicable:
  [Remotion], [veo:], [title:], [split:].
- Only write markdown spec files.

Sections to generate:
${sectionIds.map((id) => `- ${id}`).join("\n")}

Files to focus on:
${files.length > 0 ? files.map((f) => `- ${f}`).join("\n") : "ALL spec files needed per section."}
`.trim();

    const scopeDir = path.join(process.cwd(), "specs");

    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;
    progressFn?.(0);

    await runClaudeFix(prompt, scopeDir, onLog);

    progressFn?.(100);
  };
});

// ----------------------------------------------------------------------------
// POST /api/pipeline/specs/run
// ----------------------------------------------------------------------------
export async function POST(request: NextRequest): Promise<Response> {
  const body = await request.json().catch(() => ({}));
  const sections = Array.isArray(body.sections) ? body.sections : undefined;
  const files = Array.isArray(body.files) ? body.files : undefined;

  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage(
        "specs",
        { sections, files },
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