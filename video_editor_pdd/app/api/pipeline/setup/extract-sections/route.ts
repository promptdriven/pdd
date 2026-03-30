import { createSseStream } from "@/lib/sse";
import { createJob, runJob, setJobSend, clearJobSend } from "@/lib/jobs";
import { runClaudeExtract } from "@/lib/claude";
import type { Section } from "@/lib/types";

export const dynamic = "force-dynamic";

const SSE_HEADERS = {
  "Content-Type": "text/event-stream",
  "Cache-Control": "no-cache",
  Connection: "keep-alive",
};

const EXTRACT_SECTIONS_PROMPT = `You are analyzing a video production script to extract section definitions.

Instructions:
1. Read the file: narrative/main_script.md
2. Identify all ## headings that represent actual VIDEO SECTIONS.
   - Video sections typically have timestamps like (0:00 - 2:00)
   - EXCLUDE appendix/reference sections without timestamps
     (e.g., "VISUAL DESIGN NOTES", "RESEARCH CITATIONS")
3. Preserve every timed ## heading explicitly.
   - If a short timed heading logically folds into a parent pipeline section,
     keep the parent section but record the folded heading in scriptHeadings.
   - Do not destructively merge or drop timed headings from the narrative structure.
4. Return a JSON array of section objects.

For each section, generate:
- id: snake_case (e.g., "cold_open", "part1_economics")
- label: Short human-readable (e.g., "Cold Open", "Part 1: Economics")
- videoFile: "{id}.mp4"
- specDir: same as id
- remotionDir: "S{NN}-{PascalCase}" zero-padded (e.g., "S00-ColdOpen")
- compositionId: PascalCase (e.g., "ColdOpenSection", "Part1Economics")
- durationSeconds: 0
- offsetSeconds: 0
- scriptHeadings: optional array of timed ## headings owned by this section when
  multiple narrative headings fold into one pipeline section

Return ONLY a JSON array.`;

/**
 * POST /api/pipeline/setup/extract-sections
 * Runs Claude extraction to parse sections from the main script.
 * Streams progress via SSE and emits the extracted sections array.
 */
export async function POST(_request: Request): Promise<Response> {
  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = createJob("setup", {});
      setJobSend(jobId, send);

      let extractedSections: Section[] = [];

      try {
        await runJob(jobId, async (onLog) => {
          extractedSections = await runClaudeExtract<Section[]>(
            EXTRACT_SECTIONS_PROMPT,
            onLog
          );
          if (!Array.isArray(extractedSections)) {
            throw new Error("Claude did not return a valid sections array");
          }
          onLog(`Extracted ${extractedSections.length} sections`);
        });
      } finally {
        clearJobSend(jobId);
      }

      send({ type: "sections", sections: extractedSections, jobId });
      send({ type: "complete", jobId });
      done();
    } catch (err) {
      error(err instanceof Error ? err.message : "Unknown error");
    }
  })();

  return new Response(stream, { status: 202, headers: SSE_HEADERS });
}
