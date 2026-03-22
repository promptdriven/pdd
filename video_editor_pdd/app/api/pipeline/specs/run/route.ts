import { NextRequest } from "next/server";
import fs from "fs";
import path from "path";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";
import { runClaudeFix } from "@/lib/claude";
import { loadProject, saveProject } from "@/lib/project";
import {
  isDeterministicPipelineMode,
  writeDeterministicSpecsForSection,
} from "@/lib/deterministic-pipeline";
import {
  findMatchingScriptSectionVisualIntent,
  parseScriptSectionVisualIntent,
  resolveSectionVisualIntent,
} from "@/app/api/pipeline/_lib/script-visual-intent";
import { getProjectDir } from "@/lib/projects";
import { syncInferredVeoReferencesFromProjectSpecs } from "@/lib/veo-references";

const BASE_SPECS_TIMEOUT_MS = 600_000;
const SPECS_FINALIZATION_BUFFER_MS = 60_000;
const MAX_SPECS_TIMEOUT_MS = 1_500_000;

function normalizeSectionSpecDir(specDir: string): string {
  return specDir.replace(/^specs[\\/]/, "").replace(/\\/g, "/").replace(/^\/+/, "");
}

function normalizeRequestedSpecPath(filePath: string): string {
  const normalized = filePath.replace(/\\/g, "/").replace(/^\.?\//, "");
  return normalized.startsWith("specs/") ? normalized : `specs/${normalized}`;
}

function buildRequestedFilesBySection(
  sectionSpecDirs: Map<string, string>,
  requestedFiles: string[]
): Map<string, string[]> {
  const bySection = new Map<string, string[]>();

  for (const requestedFile of requestedFiles.map(normalizeRequestedSpecPath)) {
    for (const [sectionId, specDir] of sectionSpecDirs.entries()) {
      const normalizedSpecDir = normalizeSectionSpecDir(specDir);
      const expectedPrefix = `specs/${normalizedSpecDir}/`;
      if (!requestedFile.startsWith(expectedPrefix)) {
        continue;
      }

      const existing = bySection.get(sectionId) ?? [];
      existing.push(requestedFile);
      bySection.set(sectionId, existing);
      break;
    }
  }

  return bySection;
}

function estimateSpecsTimeoutMs(params: {
  specMd: string;
  scriptBody: string;
  visualIntentMode: "remotion_only" | "hybrid" | "veo_favored" | "unknown";
  hasWords: boolean;
  visualBeatCount: number;
}): number {
  const combinedLength = params.specMd.length + params.scriptBody.length;
  const extraChars = Math.max(0, combinedLength - 20_000);
  const extraCharBuckets = Math.floor(extraChars / 10_000);
  const estimatedSpecCount = Math.min(12, Math.max(4, Math.ceil(params.visualBeatCount / 2)));
  const visualComplexityBonusMs =
    params.visualIntentMode === "veo_favored"
      ? 120_000
      : params.visualIntentMode === "hybrid"
        ? 60_000
        : 0;
  const extraVisualBeats = Math.max(0, params.visualBeatCount - 8);
  const visualBeatBonusMs =
    params.visualIntentMode === "veo_favored"
      ? Math.min(360_000, Math.ceil(extraVisualBeats / 4) * 60_000)
      : params.visualIntentMode === "hybrid"
        ? Math.min(300_000, Math.ceil(extraVisualBeats / 4) * 60_000)
        : params.visualIntentMode === "remotion_only"
          ? Math.min(180_000, Math.ceil(extraVisualBeats / 4) * 30_000)
          : 0;
  const multiSpecBonusMs = Math.min(
    120_000,
    Math.max(0, estimatedSpecCount - 6) * 15_000
  );
  const timestampBonusMs = params.hasWords ? 30_000 : 0;
  const scaledTimeoutMs =
    BASE_SPECS_TIMEOUT_MS +
    SPECS_FINALIZATION_BUFFER_MS +
    extraCharBuckets * 120_000 +
    visualComplexityBonusMs +
    visualBeatBonusMs +
    multiSpecBonusMs +
    timestampBonusMs;

  return Math.min(MAX_SPECS_TIMEOUT_MS, scaledTimeoutMs);
}

function resetSectionSpecDir(sectionSpecDir: string): void {
  const veoJsonPath = path.join(sectionSpecDir, "veo.json");
  let veoJsonBackup: string | null = null;

  if (fs.existsSync(veoJsonPath)) {
    veoJsonBackup = fs.readFileSync(veoJsonPath, "utf-8");
  }

  if (fs.existsSync(sectionSpecDir)) {
    fs.rmSync(sectionSpecDir, { recursive: true, force: true });
  }
  fs.mkdirSync(sectionSpecDir, { recursive: true });

  if (veoJsonBackup !== null) {
    fs.writeFileSync(veoJsonPath, veoJsonBackup);
  }
}

function resetRequestedSpecFiles(
  specsBase: string,
  sectionSpecDir: string,
  requestedFiles: string[]
): void {
  fs.mkdirSync(sectionSpecDir, { recursive: true });
  const normalizedSectionDir = path.resolve(sectionSpecDir);

  for (const requestedFile of requestedFiles) {
    const requestedAbsPath = path.resolve(
      specsBase,
      normalizeRequestedSpecPath(requestedFile).replace(/^specs\//, "")
    );

    if (
      requestedAbsPath !== normalizedSectionDir &&
      !requestedAbsPath.startsWith(`${normalizedSectionDir}${path.sep}`)
    ) {
      continue;
    }

    fs.rmSync(requestedAbsPath, { force: true });
  }
}

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

    const files =
      Array.isArray(params.files) && params.files.length > 0
        ? (params.files as string[])
        : [];
    const requestedFilesBySection = buildRequestedFilesBySection(specDirMap, files);
    const sectionIds =
      Array.isArray(params.sections) && params.sections.length > 0
        ? (params.sections as string[])
        : requestedFilesBySection.size > 0
          ? allSectionIds.filter((sid) => requestedFilesBySection.has(sid))
          : allSectionIds;

    if (files.length > 0 && sectionIds.length === 0) {
      throw new Error(`No sections matched requested spec files: ${files.join(", ")}`);
    }

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

    const scriptVisualIntentSections = mainScriptContent
      ? parseScriptSectionVisualIntent(mainScriptContent)
      : [];

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
    const failures: Array<{ sid: string; message: string }> = [];
    const workerCount = Math.min(2, sectionIds.length || 1);

    const runSection = async (): Promise<void> => {
      while (true) {
        const currentIndex = nextIndex++;
        if (currentIndex >= sectionIds.length) {
          return;
        }

        const sid = sectionIds[currentIndex];
        const dir = specDirMap.get(sid) ?? sid;
        const sectionFiles = requestedFilesBySection.get(sid) ?? [];
        const section = sectionMap.get(sid);
        const ctx = sectionContextMap.get(sid)!;
        const matchingScriptSection =
          section && scriptVisualIntentSections.length > 0
            ? findMatchingScriptSectionVisualIntent(scriptVisualIntentSections, {
                id: section.id,
                label: section.label,
              })
            : null;
        const visualIntent =
          section && mainScriptContent
            ? resolveSectionVisualIntent(mainScriptContent, {
                id: section.id,
                label: section.label,
              })
            : null;
        const timeoutMs = estimateSpecsTimeoutMs({
          specMd: ctx.specMd,
          scriptBody: matchingScriptSection?.bodyLines.join("\n") ?? "",
          visualIntentMode: visualIntent?.mode ?? "unknown",
          hasWords: ctx.hasWords,
          visualBeatCount: matchingScriptSection?.visualLines.length ?? 0,
        });
        const sectionSpecDir = path.join(specsBase, dir);

        onLog(
          `[specs] Generating specs for section: ${sid} (${currentIndex + 1}/${sectionIds.length})`
        );
        if (sectionFiles.length > 0) {
          resetRequestedSpecFiles(specsBase, sectionSpecDir, sectionFiles);
        } else {
          resetSectionSpecDir(sectionSpecDir);
        }

        const sectionContext = `
### Section: ${sid} → specs/${dir}/
${ctx.specMd ? `\nNarrative arc (spec.md):\n${ctx.specMd}\n` : "(No spec.md found — infer visual needs from section name.)"}
${ctx.hasWords ? `Word timestamps available at: data/${sid}_words.json (use for frame-accurate timing)` : "(No word timestamps available yet.)"}
`;

        const sectionVisualGuidance =
          visualIntent?.mode === "remotion_only"
            ? `
This section appears primarily abstract, diagrammatic, or UI-driven based on main_script.md.
Avoid [veo:] unless a beat clearly requires cinematic footage.
Use [Remotion], [title:], and [split:] only for this section.
A typical section here should lean on 3-6 [Remotion] animations plus 1-2 [title:] or [split:] cards.
`.trim()
            : visualIntent?.explicitVeo
              ? `
This section explicitly includes [veo:] footage in main_script.md.
Include at least one [veo:] spec and align it to the quoted script beat that calls for footage.
Mix [veo:] with [Remotion], [title:], and [split:] only where the script supports it.
A typical section here should have a mix: 2-4 [Remotion] animations, 1-3 [veo:] clips, and 1-2 [title:] or [split:] cards.
`.trim()
              : visualIntent?.mode === "hybrid" || visualIntent?.mode === "veo_favored"
                ? `
This section includes cinematic or live-action beats in main_script.md even without explicit [veo:] markers.
Decide scene-by-scene whether each beat is better as [veo:], [Remotion], [title:], or [split:].
Include at least one [veo:] spec for the cinematic beats.
Use [Remotion] for charts, diagrams, code UI, data overlays, and abstract explanatory visuals.
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
Each spec file describes ONE visual component with enough detail for a developer to implement or generate it.

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
- For [Remotion] specs, use **Tool:** Remotion.
- For [veo:] specs, use **Tool:** Veo (cinematic B-roll) or **Tool:** Veo.
- For [title:] specs, use **Tool:** Title.
- For [split:] specs, use **Tool:** Split.
- IMPORTANT: If a [split:] or other composition spec embeds Veo video clips (e.g., a split-screen
  showing live-action footage in each panel), you MUST also generate separate companion [veo:] spec
  files for EACH embedded clip. The Veo generation pipeline only discovers standalone [veo:] specs —
  clips referenced inside [split:] or [Remotion] specs will NOT be generated unless they have their
  own dedicated [veo:] spec file. Name companions like {NN}_{clip_id}.md with a [veo:] marker.
- For EVERY [veo:] spec, use this exact canonical structure:
  - first line must be exactly: [veo:]
  - include a dedicated heading: ### Veo Prompt
  - place the full natural-language Veo generation prompt inside a fenced code block under ### Veo Prompt
  - include ## Data Points JSON with at least: { "type": "veo_clip", "clipId": "{snake_case_clip_id}" }
  - when the same human character/person recurs across multiple [veo:] specs or must stay visually consistent, include:
    "characters": [{ "id": "{snake_case_character_id}", "label": "{Display Name}", "referencePrompt": "{portrait/reference description}" }]
  - include characters ONLY for recurring or consistency-critical people, not one-off background extras
  - Do NOT put the natural-language Veo prompt inline inside the [veo:] marker.
  - IMPORTANT: Each Veo prompt must describe a single continuous action or moment, NOT a multi-step
    sequence. Veo models cannot reliably produce complex multi-phase action sequences (e.g.
    "examine → toss → grab → hold") in a single 8-second clip. Instead, describe ONE key visual
    moment or action. Avoid chaining multiple distinct actions — if a scene requires multiple
    phases, split them into separate [veo:] specs.
${sectionVisualGuidanceList}
- You should generate at least 4-8 spec files per section.
${sectionFiles.length > 0 ? `- Only generate these specific files: ${sectionFiles.join(", ")}` : "- Generate ALL spec files needed for the section."}

REQUIRED SPEC FORMAT — each spec file MUST include ALL of these sections:

# Section N.N: {Component Name}

**Tool:** {Remotion | Veo | Title | Split}
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

## Data Points JSON
\`\`\`json
{ "series": [...] }
\`\`\`

---

${sectionContext}
`.trim();

        try {
          await runClaudeFix(prompt, specsBase, onLog, { timeoutMs });
          completedSections += 1;
          const pct = Math.round((completedSections / totalSections) * 100);
          progressFn?.(pct);
          onLog(`[specs] Section ${sid} complete (${pct}%)`);
        } catch (err) {
          const message =
            err instanceof Error ? err.message : "Unknown spec generation error";
          failures.push({ sid, message });
          completedSections += 1;
          const pct = Math.round((completedSections / totalSections) * 100);
          progressFn?.(pct);
          onLog(`[specs] Section ${sid} failed (${pct}%): ${message}`);
        }
      }
    };

    await Promise.all(
      Array.from({ length: workerCount }, () => runSection())
    );

    if (failures.length > 0) {
      const message = `Spec generation failed for ${failures.length} section(s): ${failures
        .map((failure) => `${failure.sid} (${failure.message})`)
        .join(", ")}`;
      onLog(`[specs] ${message}`);
      throw new Error(message);
    }

    const syncedConfig = syncInferredVeoReferencesFromProjectSpecs(getProjectDir(), cfg);
    const previousReferences = JSON.stringify(cfg.veo.references ?? []);
    const nextReferences = JSON.stringify(syncedConfig.veo.references ?? []);
    if (previousReferences !== nextReferences) {
      saveProject(syncedConfig, getProjectDir());
      onLog(
        `[specs] Synced ${(syncedConfig.veo.references ?? []).length} Veo reference entr${(syncedConfig.veo.references ?? []).length === 1 ? "y" : "ies"} to project.json`
      );
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
