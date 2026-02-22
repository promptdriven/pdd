// app/api/pipeline/tts-script/run/route.ts
import path from "path";
import { createSseStream } from "@/lib/sse";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { runClaudeFix } from "@/lib/claude";

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

You are allowed to read/write files ONLY in the narrative/ directory.
`;

/**
 * Register executor for tts-script stage.
 * Uses runClaudeFix scoped to the narrative/ directory.
 */
registerExecutor("tts-script", (_params, _send) => {
  return async (onLog) => {
    await runClaudeFix(
      TTS_SCRIPT_PROMPT,
      path.join(process.cwd(), "narrative"),
      onLog
    );
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
      const jobId = await runPipelineStage("tts-script", {}, send);

      // First SSE event includes jobId
      send({ type: "started", jobId });

      // Completion event
      send({ type: "complete", jobId });
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