import { NextRequest } from "next/server";
import fs from "fs";
import path from "path";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";
import { runClaudeFix } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import {
  isDeterministicPipelineMode,
  writeDeterministicSpecsForSection,
} from "@/lib/deterministic-pipeline";
import { resolveSectionHasVeoIntent } from "@/app/api/pipeline/_lib/script-visual-intent";
import { getProjectDir } from "@/lib/projects";

// ----------------------------------------------------------------------------
// Register specs executor (runs Claude scoped to /specs)
// ----------------------------------------------------------------------------
registerExecutor("specs", (params, _send) => {
  return async (onLog) => {
    const cfg = loadProject();
    const allSectionIds = cfg.sections.map((s) => s.id);
    const sectionMap = new Map(cfg.sections.map((section) => [section.id, section]));

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

    const specsBase = path.join(getProjectDir(), "specs");
    const dataDir = path.join(getProjectDir(), "data");
    const mainScriptPath = path.join(getProjectDir(), "narrative", "main_script.md");
    let mainScriptContent: string | null = null;

    if (fs.existsSync(mainScriptPath)) {
      try {
        mainScriptContent = fs.readFileSync(mainScriptPath, "utf-8");
      } catch {
        mainScriptContent = null;
      }
    }

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

    const totalSections = sectionIds.length || 1;

    if (isDeterministicPipelineMode()) {
      sectionIds.forEach((sid, index) => {
        const section = cfg.sections.find((candidate) => candidate.id === sid);
        if (!section) {
          return;
        }

        onLog(`[specs] Generating specs for section: ${sid} (${index + 1}/${sectionIds.length})`);
        writeDeterministicSpecsForSection(getProjectDir(), section, onLog);
        const pct = Math.round(((index + 1) / totalSections) * 100);
        progressFn?.(pct);
        onLog(`[specs] Section ${sid} complete (${pct}%)`);
      });
      return;
    }

    let completedSections = 0;
    let nextIndex = 0;
    const workerCount = Math.min(2, sectionIds.length || 1);

    const runSection = async (): Promise<void> => {
      const currentIndex = nextIndex++;
      if (currentIndex >= sectionIds.length) {
        return;
      }

      const sid = sectionIds[currentIndex];
      const dir = specDirMap.get(sid) ?? sid;
      const section = sectionMap.get(sid);
      const ctx = sectionContextMap.get(sid)!;
      const hasVeoIntent =
        section && mainScriptContent
          ? resolveSectionHasVeoIntent(mainScriptContent, {
              id: section.id,
              label: section.label,
            })
          : null;

      onLog(`[specs] Generating specs for section: ${sid} (${currentIndex + 1}/${sectionIds.length})`);

      const sectionContext = `
### Section: ${sid} → specs/${dir}/
${ctx.specMd ? `\nNarrative arc (spec.md):\n${ctx.specMd}\n` : "(No spec.md found — infer visual needs from section name.)"}
${ctx.hasWords ? `Word timestamps available at: data/${sid}_words.json (use for frame-accurate timing)` : "(No word timestamps available yet.)"}
`;

      const sectionVisualGuidance =
        hasVeoIntent === false
          ? `
This section does NOT use Veo footage in main_script.md.
Do NOT create any [veo:] specs for this section.
Use [Remotion], [title:], and [split:] only for this section.
A typical section here should lean on 3-6 [Remotion] animations plus 1-2 [title:] or [split:] cards.
`.trim()
          : hasVeoIntent === true
            ? `
This section explicitly includes [veo:] footage in main_script.md.
Include at least one [veo:] spec and align it to the quoted script beat that calls for footage.
Mix [veo:] with [Remotion], [title:], and [split:] only where the script supports it.
A typical section here should have a mix: 2-4 [Remotion] animations, 1-3 [veo:] clips, and 1-2 [title:] or [split:] cards.
`.trim()
            : `
Script intent could not be resolved for this section, so infer the right mix from the section narrative.
A typical section should have a mix: 2-4 [Remotion] animations, 2-3 [veo:] clips, and 1-2 [title:] or [split:] cards when the script suggests cinematic footage.
`.trim();

      const sectionVisualGuidanceList = sectionVisualGuidance
        .split("\n")
        .filter(Boolean)
        .map((line) => `- ${line}`)
        .join("\n");

      const prompt = `
You are generating rich visual spec markdown files for a video pipeline.
Each spec file describes ONE animated Remotion component with enough detail for a developer to implement it.

CRITICAL: You MUST create MULTIPLE separate files — one per visual component.
DO NOT create a single spec.md or any single monolithic file.

Instructions:
- Generate specs ONLY under: specs/${dir}/
- Create one file per visual component: {NN}_{snake_case_name}.md
  where NN is a zero-padded sequence number (01, 02, 03, ...).
  Example filenames: 01_cost_graph.md, 02_debt_timeline.md, 03_stat_callout_github.md
- Each file MUST start with a visual type marker on the FIRST line. Use a MIX of types:
  [Remotion] — for animated chart, graph, infographic, or data visualization components
  [veo:] — for cinematic video footage or B-roll (live-action style, no data overlay)
  [title:] — for title cards, section headers, or text-only screens
  [split:] — for split-screen comparison layouts
${sectionVisualGuidanceList}
- You should generate at least 4-8 spec files per section.
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

      completedSections += 1;
      const pct = Math.round((completedSections / totalSections) * 100);
      progressFn?.(pct);
      onLog(`[specs] Section ${sid} complete (${pct}%)`);
      await runSection();
    };

    await Promise.all(
      Array.from({ length: workerCount }, () => runSection())
    );
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
