// app/api/pipeline/tts-script/run/route.ts
import fs from "fs";
import path from "path";
import { createSseStream } from "@/lib/sse";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { runClaudeFix } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import { getProjectDir } from "@/lib/projects";
import { buildCanonicalTtsScript } from "@/lib/tts-script-format";
import {
  isDeterministicPipelineMode,
  writeDeterministicTtsScript,
} from "@/lib/deterministic-pipeline";

export const dynamic = "force-dynamic";

/**
 * Prompt instructing Claude to generate narrative/tts_script.md
 * from narrative/main_script.md by extracting narrator blocks and
 * adding TTS annotation markers.
 */
const TTS_SCRIPT_PROMPT = `
You are generating a TTS (text-to-speech) script for the video pipeline.

Instructions:
1. Read the file: narrative/main_script.md
2. Extract ONLY the NARRATOR: blocks (and their text).
3. For each narration block, add TTS annotation markers:
   - [TONE: ...]
   - [PACE: ...]
   - [PAUSE: ...]
   - [EMOTION: ...]
4. Write the final TTS script to: narrative/tts_script.md
5. Keep the result clean and readable in Markdown.
6. Do not include non-spoken labels such as Block 1, Scene 2, Section headings, or editorial numbering in the spoken narration.
7. Do not include markdown emphasis markers or other formatting punctuation in spoken lines. Output only spoken narration text plus TTS annotation tags.
8. The final file must use a stable machine-readable section-based format:
   - preserve the spoken-block order from the source script
   - emit ## section headings for each project section
   - under each section, emit annotation tags plus only the spoken narration text

You are allowed to read/write files ONLY in the narrative/ directory.
`;

/**
 * Register executor for tts-script stage.
 * Uses runClaudeFix scoped to the narrative/ directory.
 */
registerExecutor("tts-script", (_params, _send) => {
  return async (onLog) => {
    const projectDir = getProjectDir();
    const project = loadProject();
    if (isDeterministicPipelineMode()) {
      writeDeterministicTtsScript(projectDir, project.sections, onLog);
      return;
    }

    await runClaudeFix(
      TTS_SCRIPT_PROMPT,
      path.join(projectDir, "narrative"),
      onLog
    );

    const narrativeDir = path.join(projectDir, "narrative");
    const mainScriptPath = path.join(narrativeDir, "main_script.md");
    const ttsScriptPath = path.join(narrativeDir, "tts_script.md");
    const mainScript = fs.existsSync(mainScriptPath)
      ? fs.readFileSync(mainScriptPath, "utf-8")
      : "";
    const rawTtsScript = fs.existsSync(ttsScriptPath)
      ? fs.readFileSync(ttsScriptPath, "utf-8")
      : "";

    const canonicalScript = buildCanonicalTtsScript(
      mainScript,
      rawTtsScript,
      project.sections,
    );
    fs.mkdirSync(narrativeDir, { recursive: true });
    fs.writeFileSync(ttsScriptPath, canonicalScript, "utf-8");
    onLog("[tts-script] Normalized tts_script.md to canonical section format.");
  };
});

/**
 * POST /api/pipeline/tts-script/run
 * Runs tts-script stage with SSE streaming.
 */
export async function POST(_request: Request): Promise<Response> {
  const { stream, send, done, error } = createSseStream();

  // Fire-and-forget execution with SSE progress
  (async () => {
    try {
      // Wrap the send callback to capture the jobId from the first log event
      // and send a "started" event immediately, before the job finishes.
      let jobId: string | null = null;
      const wrappedSend = (data: object) => {
        const rec = data as Record<string, unknown>;
        if (!jobId && rec.jobId) {
          jobId = rec.jobId as string;
          send({ type: "started", jobId });
        }
        send(data);
      };

      await runPipelineStage("tts-script", {}, wrappedSend);

      // Completion event
      if (jobId) {
        send({ type: "complete", jobId });
      }
      done();
    } catch (err) {
      const message =
        err instanceof Error ? err.message : "Unknown error running tts-script";
      error(message);
    }
  })();

  return new Response(stream, {
    status: 202,
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}
