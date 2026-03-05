import { NextRequest } from "next/server";
import fs from "fs";
import path from "path";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";
import { runClaudeFix } from "@/lib/claude";
import { loadProject } from "@/lib/project";

// ----------------------------------------------------------------------------
// Register specs executor (runs Claude scoped to /specs)
// ----------------------------------------------------------------------------
registerExecutor("specs", (params, _send) => {
  return async (onLog) => {
    const cfg = loadProject();
    const allSectionIds = cfg.sections.map((s) => s.id);

    // Map section ID → specDir from project config (list API uses specDir)
    const specDirMap = new Map<string, string>();
    for (const s of cfg.sections) {
      specDirMap.set(s.id, s.specDir);
    }

    const sectionIds =
      Array.isArray(params.sections) && params.sections.length > 0
        ? (params.sections as string[])
        : allSectionIds;

    const files =
      Array.isArray(params.files) && params.files.length > 0
        ? (params.files as string[])
        : [];

    const specsBase = path.join(process.cwd(), "specs");
    const dataDir = path.join(process.cwd(), "data");

    // Read spec.md and word timestamps BEFORE cleaning, so the narrative
    // context survives the stale-file purge.
    const sectionContextMap = new Map<string, { specMd: string; hasWords: boolean }>();
    for (const sid of sectionIds) {
      const dir = specDirMap.get(sid) ?? sid;
      const specMdPath = path.join(specsBase, dir, "spec.md");
      let specMdContent = "";
      if (fs.existsSync(specMdPath)) {
        try { specMdContent = fs.readFileSync(specMdPath, "utf-8"); } catch { /* ignore */ }
      }
      const wordsPath = path.join(dataDir, `${sid}_words.json`);
      sectionContextMap.set(sid, {
        specMd: specMdContent,
        hasWords: fs.existsSync(wordsPath),
      });
    }

    // Clean stale spec files for sections being regenerated so Claude CLI
    // doesn't waste time reading/deconflicting with old content.
    // Preserve veo.json (Veo prompt overrides placed by users or tests).
    for (const sid of sectionIds) {
      const dir = specDirMap.get(sid) ?? sid;
      const sectionSpecDir = path.join(specsBase, dir);
      if (fs.existsSync(sectionSpecDir)) {
        const veoJsonPath = path.join(sectionSpecDir, "veo.json");
        let veoJsonBackup: string | null = null;
        if (fs.existsSync(veoJsonPath)) {
          veoJsonBackup = fs.readFileSync(veoJsonPath, "utf-8");
        }
        fs.rmSync(sectionSpecDir, { recursive: true, force: true });
        fs.mkdirSync(sectionSpecDir, { recursive: true });
        if (veoJsonBackup !== null) {
          fs.writeFileSync(veoJsonPath, veoJsonBackup);
        }
      } else {
        fs.mkdirSync(sectionSpecDir, { recursive: true });
      }
    }

    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;
    progressFn?.(0);

    // Generate specs one section at a time so each Claude invocation has a
    // focused task and we get per-section progress updates.
    for (let i = 0; i < sectionIds.length; i++) {
      const sid = sectionIds[i];
      const dir = specDirMap.get(sid) ?? sid;
      const ctx = sectionContextMap.get(sid)!;

      onLog(`[specs] Generating specs for section: ${sid} (${i + 1}/${sectionIds.length})`);

      const sectionContext = `
### Section: ${sid} → specs/${dir}/
${ctx.specMd ? `\nNarrative arc (spec.md):\n${ctx.specMd}\n` : "(No spec.md found — infer visual needs from section name.)"}
${ctx.hasWords ? `Word timestamps available at: data/${sid}_words.json (use for frame-accurate timing)` : "(No word timestamps available yet.)"}
`;

      const prompt = `
You are generating rich visual spec markdown files for a video pipeline.
Each spec file describes ONE animated Remotion component with enough detail for a developer to implement it.

Instructions:
- Generate specs ONLY under: specs/${dir}/
- Use the visual type marker [Remotion] on the FIRST line for animated components.
  Other markers: [veo:], [title:], [split:].
- Decompose the section into standalone numbered spec files: {NN}_{snake_case_name}.md
  where NN is a zero-padded sequence number (01, 02, 03, ...).
${files.length > 0 ? `- Only generate these specific files: ${files.join(", ")}` : "- Generate ALL spec files needed for the section."}

REQUIRED SPEC FORMAT — each spec file MUST include ALL of these sections:

# Section N.N: {Component Name}

**Tool:** Remotion
**Duration:** ~Xs
**Timestamp:** M:SS - M:SS

## Visual Description
(What the viewer sees — animated chart, graph, infographic, etc.)

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: {color with hex code}
- Grid lines: {if applicable}

### Chart/Visual Elements
- (Describe each visual element: axes, lines, bars, shapes, with colors, positions, data ranges)

### Animation Sequence
1. **Frame 0-30 (0-1s):** {what animates}
2. **Frame 30-90 (1-3s):** {what animates}
(Continue for each animation beat)

### Typography
- Title: {font, size, color}
- Labels: {font, size, color, opacity}

### Easing
- {animation name}: \`{easing function}\` (e.g., easeInOutCubic, easeOutQuad)

## Narration Sync
> "{exact quoted narration text that triggers this visual}"

## Code Structure (Remotion)
\`\`\`typescript
<Sequence from={0} durationInFrames={N}>
  <ComponentA />
  <Sequence from={M}>
    <SubComponent data={...} />
  </Sequence>
</Sequence>
\`\`\`

## Data Points
\`\`\`json
{ "series": [...] }
\`\`\`

---

${sectionContext}
`.trim();

      await runClaudeFix(prompt, specsBase, onLog);

      const pct = Math.round(((i + 1) / sectionIds.length) * 100);
      progressFn?.(pct);
      onLog(`[specs] Section ${sid} complete (${pct}%)`);
    }
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