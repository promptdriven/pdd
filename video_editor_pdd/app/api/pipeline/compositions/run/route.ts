import { NextRequest } from "next/server";
import path from "path";
import fs from "fs";
import os from "os";
import { spawn, execSync } from "child_process";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";
import { runClaudeFix } from "@/lib/claude";
import { buildSectionConstantsSource } from "@/lib/composition-timing";
import { loadProject, saveProject } from "@/lib/project";
import {
  getAppRemotionDir,
  getAppRemotionPublicDir,
  getAppRemotionSrcDir,
  getAppScriptsDir,
  getProjectDir,
} from "@/lib/projects";
import { renderStill } from "@/lib/render";
import type { Section, SseSend } from "@/lib/types";
import {
  isDeterministicPipelineMode,
  writeDeterministicComponent,
  writeDeterministicSectionConstants,
} from "@/lib/deterministic-pipeline";

type SectionComponentEntry = {
  sectionId: string;
  components: string[];
};

type RunBody = {
  components?: string[];
  wrappers?: string[];
  sectionId?: string;
  sectionComponents?: SectionComponentEntry[];
};

type SectionComposition = NonNullable<Section["compositions"]>[number];

const getRemotionScopeDir = () => getAppRemotionSrcDir();
const getSpecsDir = () => path.join(getProjectDir(), "specs");

/** Names that are section-level metadata, not visual components. */
const NON_COMPONENT_BASENAMES = new Set(["spec", "veo"]);

function hasAuthoredSectionTimeline(section: Pick<Section, "id" | "compositionId">): boolean {
  const sectionPascal = toPascalCase(section.id);
  const componentName = `${sectionPascal}Section`;
  const remotionSrc = getAppRemotionSrcDir();
  const candidates = [
    path.join(remotionSrc, section.id, `${section.compositionId}.tsx`),
    path.join(remotionSrc, section.id, `${componentName}.tsx`),
    path.join(remotionSrc, `${section.compositionId}.tsx`),
    path.join(remotionSrc, `${componentName}.tsx`),
  ];

  return candidates.some((candidate) => fs.existsSync(candidate));
}

// ---------------------------------------------------------------------------
// Utility: find spec file content for a component (best effort)
// ---------------------------------------------------------------------------
function findSpecForComponent(componentName: string, sectionSpecDir?: string): string {
  const specsDir = getSpecsDir();
  if (!fs.existsSync(specsDir)) return "";

  // When a section specDir is provided, search there first for an exact match
  if (sectionSpecDir) {
    const absDir = path.isAbsolute(sectionSpecDir)
      ? sectionSpecDir
      : path.join(getProjectDir(), sectionSpecDir);
    if (fs.existsSync(absDir)) {
      for (const ext of [".md", ".txt", ".tsx"]) {
        const candidate = path.join(absDir, `${componentName}${ext}`);
        if (fs.existsSync(candidate)) {
          try { return fs.readFileSync(candidate, "utf-8"); } catch { /* fall through */ }
        }
      }
    }
  }

  // Handle fallback names like "animation_section_main" — map to specs/{sectionId}/spec.md
  if (componentName.endsWith("_main")) {
    const sectionId = componentName.slice(0, -"_main".length);
    const specMd = path.join(specsDir, sectionId, "spec.md");
    if (fs.existsSync(specMd)) {
      try { return fs.readFileSync(specMd, "utf-8"); } catch { /* fall through */ }
    }
  }

  const matches: string[] = [];

  const walk = (dir: string) => {
    const entries = fs.readdirSync(dir, { withFileTypes: true });
    for (const entry of entries) {
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(p);
      if (entry.isFile()) {
        const base = path.basename(entry.name, path.extname(entry.name));
        if (base === componentName) matches.push(p);
      }
    }
  };

  walk(specsDir);

  if (!matches.length) return "";
  try {
    return fs.readFileSync(matches[0], "utf-8");
  } catch {
    return "";
  }
}

// ---------------------------------------------------------------------------
// Claude prompt factory
// ---------------------------------------------------------------------------
function listVeoAssets(): string[] {
  const veoPublicDir = path.join(getAppRemotionPublicDir(), "veo");
  if (!fs.existsSync(veoPublicDir)) return [];
  return fs.readdirSync(veoPublicDir).filter((f) => f.endsWith(".mp4") || f.endsWith(".webm"));
}

function buildComponentPrompt(baseName: string, outputName: string, spec: string, veoAssets: string[]): string {
  const veoSection = veoAssets.length > 0
    ? `\n--- VEO ASSETS ---\nThe following video files are available in remotion/public/veo/.\nUse staticFile("veo/<filename>") to reference them (NOT staticFile("public/veo/...")).\n${veoAssets.map((f) => `- ${f}`).join("\n")}\n--- END VEO ASSETS ---\n`
    : "";

  const exportName = toPascalCase(outputName);
  // Use exportName as directory name to match what Claude Code actually creates.
  // Previously used NN-PascalName format (e.g., "05-CrossfadeTransition") but Claude
  // would create section-prefixed dirs (e.g., "ColdOpen05CrossfadeTransition") instead,
  // causing a mismatch that broke discovery.
  const dirName = exportName;

  return `
You are Claude Code. Generate a Remotion animation component as a multi-file directory.

Component name: ${baseName}
Export name: ${exportName}

OUTPUT STRUCTURE — create a subdirectory with multiple files:
  remotion/src/remotion/${dirName}/
    ├── ${exportName}.tsx          (main component)
    ├── constants.ts               (component-level constants, colors, dimensions)
    ├── index.ts                   (barrel export: export { ${exportName}, default${exportName}Props } from './${exportName}')
    └── (optional sub-components like AnimatedLine.tsx, ChartAxes.tsx, etc.)

CRITICAL EXPORT REQUIREMENT:
- index.ts MUST re-export the main component as BOTH named and default: export { ${exportName} } from './${exportName}'; export { default } from './${exportName}';
- The main TSX MUST export as: export const ${exportName}: React.FC = () => { ... }; export default ${exportName};
- Also export default props: export const default${exportName}Props = {};

CRITICAL RENDERING REQUIREMENTS:
- The component MUST render visible content from frame 0 (no delayed fade-ins).
- Use an <AbsoluteFill> with a non-black background color (e.g., "#0A1628" dark navy).
- All animated elements must use bright, high-contrast colors (e.g., white, bright blue #3B82F6, green #22C55E).
- Every visual element must have explicit width, height, and position.
- Use only supported Remotion easing APIs. For quartic easing, use Easing.poly(4), NOT Easing.quart.
- Do NOT import external data files (e.g., JSON word timestamps) that may not exist.
  If subtitles are needed, embed word data inline or skip subtitles.
- If the component needs Veo media, import useVisualMediaSrc from ../_shared/visual-runtime
  and resolve media via that hook instead of hardcoding staticFile("veo/<section>.mp4").
  Wrapper code will provide per-visual media aliases like backgroundSrc, outputSrc,
  leftSrc, rightSrc, baseSrc, and revealSrc.
- Only import from "remotion" — do not import from other local files in the component directory.
- Break complex visuals into sub-components (e.g., AnimatedLine.tsx, ChartAxes.tsx) for maintainability.

Use the spec below to implement the component accurately.

--- SPEC ---
${spec || "(spec not found, infer from naming)"}
--- END SPEC ---
${veoSection}
Return valid TypeScript/React code.
`;
}

// ---------------------------------------------------------------------------
// Generate section constants.ts with BEATS / VISUAL_SEQUENCE
// ---------------------------------------------------------------------------
async function generateSectionConstants(
  section: Pick<Section, "id" | "specDir" | "durationSeconds" | "compositionId" | "compositions">,
  componentIds: string[],
  remotionDir: string,
  onLog: (msg: string) => void,
): Promise<void> {
  onLog(`[compositions] Generating section constants: ${remotionDir}/constants.ts`);
  fs.mkdirSync(remotionDir, { recursive: true });
  fs.writeFileSync(
    path.join(remotionDir, "constants.ts"),
    buildSectionConstantsSource(getProjectDir(), section, componentIds)
  );
}

// ---------------------------------------------------------------------------
// Generate section composition with activeVisual pattern
// ---------------------------------------------------------------------------
async function generateSectionComposition(
  sectionId: string,
  compositionId: string,
  componentIds: string[],
  remotionDir: string,
  onLog: (msg: string) => void,
): Promise<void> {
  const pascalCompositionId = toPascalCase(compositionId);

  // Build import list for components
  const componentImports = componentIds
    .filter((id) => !id.startsWith("veo:"))
    .map((id) => {
      const pascal = toPascalCase(id);
      const nnMatch = id.match(/^(\d{2})_/);
      const strippedPascal = nnMatch ? toPascalCase(id.slice(nnMatch[0].length)) : pascal;
      const dirName = nnMatch ? `${nnMatch[1]}-${strippedPascal}` : strippedPascal;
      return `import { ${strippedPascal}, default${strippedPascal}Props } from "../${dirName}";`;
    })
    .join("\n");

  const prompt = `
You are Claude Code. Generate a section composition TSX file using the activeVisual pattern.

Output file: ${remotionDir}/${pascalCompositionId}.tsx

This composition sequences all animation components for section "${sectionId}" using frame-accurate timing.

REQUIRED PATTERN:
1. Import React, AbsoluteFill, Audio, Loop, Sequence, OffthreadVideo, staticFile, useCurrentFrame from "remotion"
2. Import BEATS, VISUAL_SEQUENCE, ${pascalCompositionId}PropsType from "./constants"
3. Import all animation components:
${componentImports}

4. Use activeVisual pattern to switch between components:
\`\`\`typescript
export const ${pascalCompositionId}: React.FC<${pascalCompositionId}PropsType> = () => {
  const frame = useCurrentFrame();
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) { activeVisual = i; break; }
  }
  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      <Audio src={staticFile("${sectionId}/narration.wav")} />
      {/* For each visual in VISUAL_SEQUENCE: */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <ComponentName {...defaultComponentNameProps} />
        </Sequence>
      )}
      {/* For veo: entries, use OffthreadVideo with Loop and canonical public path: */}
      {activeVisual === N && (
        <Sequence from={BEATS.VISUAL_NN_START}>
          <AbsoluteFill><Loop durationInFrames={240}>
            <OffthreadVideo src={staticFile("veo/<filename>.mp4")} style={{ width: "100%", height: "100%" }} />
          </Loop></AbsoluteFill>
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
\`\`\`

MEDIA PATH CONTRACT:
- Narration audio must use staticFile("${sectionId}/narration.wav")
- Veo clips must use staticFile("veo/<filename>") using the exact filename from the available assets list
- Do not invent alternate paths like "${sectionId}_narration.wav" or bare "clip.mp4"

Component IDs in VISUAL_SEQUENCE order:
${componentIds.map((id, i) => `- Visual ${i}: ${id}${id.startsWith("veo:") ? " (use OffthreadVideo + Loop)" : ""}`).join("\n")}

Generate the complete section composition file. Include ALL visuals from VISUAL_SEQUENCE.
`.trim();

  onLog(`[compositions] Generating section composition: ${remotionDir}/${pascalCompositionId}.tsx`);
  await runClaudeFix(prompt, getRemotionScopeDir(), onLog);
}

// ---------------------------------------------------------------------------
// Fallback: generate a deterministic template component when the only spec is
// spec.md (no individual component specs). This avoids non-deterministic
// Claude output that may render all-black.
// ---------------------------------------------------------------------------
function generateFallbackComponent(
  name: string,
  spec: string,
  veoAssets: string[],
  onLog: (msg: string) => void,
): void {
  const outPath = path.join(getRemotionScopeDir(), `${name}.tsx`);

  // Check if any Veo asset matches this section (e.g., "veo_section.mp4" for "veo_section_main")
  const sectionId = name.endsWith("_main") ? name.slice(0, -"_main".length) : name;
  const matchingVeo = veoAssets.find((f) => f.startsWith(sectionId));

  let code: string;
  if (matchingVeo) {
    // Veo-backed section: show video with subtitle overlay
    code = `import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, useCurrentFrame, useVideoConfig } from "remotion";

export const ${toPascalCase(name)}: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const sec = frame / fps;

  return (
    <AbsoluteFill style={{ backgroundColor: "#000" }}>
      <OffthreadVideo
        src={staticFile("veo/${matchingVeo}")}
        style={{ width: "100%", height: "100%", objectFit: "cover" }}
      />
      <div style={{
        position: "absolute", bottom: 80, left: 0, right: 0,
        textAlign: "center", color: "#fff", fontSize: 32,
        textShadow: "0 2px 8px rgba(0,0,0,0.8)",
        fontFamily: "sans-serif",
      }}>
        {sec.toFixed(1)}s
      </div>
    </AbsoluteFill>
  );
};

export default ${toPascalCase(name)};
`;
  } else {
    // Animation-only section: render spec description as animated text + shapes
    const title = sectionId.replace(/_/g, " ").replace(/\\b\\w/g, (c) => c.toUpperCase());
    code = `import React from "react";
import { AbsoluteFill, useCurrentFrame, useVideoConfig, interpolate } from "remotion";
import { getProjectDir } from "@/lib/projects";

export const ${toPascalCase(name)}: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const progress = frame / (fps * 3);

  const circleScale = interpolate(progress, [0, 0.3, 0.5], [0, 1, 1], { extrapolateRight: "clamp" });
  const circleColor = progress < 0.5 ? "#3B82F6" : "#22C55E";
  const shapeRadius = progress >= 0.5 ? interpolate(progress, [0.5, 0.7], [50, 0], { extrapolateRight: "clamp" }) : 50;
  const slideX = progress >= 0.5 ? interpolate(progress, [0.5, 0.8], [0, 200], { extrapolateRight: "clamp" }) : 0;

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628", justifyContent: "center", alignItems: "center" }}>
      <div style={{
        width: 180, height: 180,
        backgroundColor: circleColor,
        borderRadius: shapeRadius + "%",
        transform: \`scale(\${circleScale}) translateX(\${slideX}px)\`,
      }} />
      <div style={{
        position: "absolute", bottom: 100, color: "#E2E8F0",
        fontSize: 36, fontFamily: "sans-serif", fontWeight: "bold",
        textAlign: "center",
      }}>
        ${title}
      </div>
    </AbsoluteFill>
  );
};

export default ${toPascalCase(name)};
`;
  }

  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, code);
  onLog(`[compositions] Generated fallback component: ${name}`);
}

function toPascalCase(s: string): string {
  return s.replace(/(^|_)(\w)/g, (_, __, c) => c.toUpperCase());
}

function compToRemotionId(compId: string, sectionId: string): string {
  let pascal = toPascalCase(compId);
  if (/^\d/.test(pascal)) {
    pascal = toPascalCase(sectionId) + pascal;
  }
  return pascal.replace(/([a-z0-9])([A-Z])/g, "$1-$2").toLowerCase();
}

type ProjectSectionForValidation = {
  id: string;
  compositions?: Array<string | { id: string }>;
};

type ValidationTarget = {
  componentName: string;
  sectionId: string;
  compositionId: string;
};

const shouldSkipPreviewValidation = () =>
  process.env.VIDEO_EDITOR_SKIP_COMPOSITION_VALIDATION === "1";

function resolveValidationTargets(
  componentName: string,
  preferredSectionId: string | undefined,
  sections: ProjectSectionForValidation[],
): ValidationTarget[] {
  const sectionIds = preferredSectionId
    ? [preferredSectionId]
    : sections
        .filter((section) => {
          const compIds = (section.compositions ?? []).map((comp) =>
            typeof comp === "string" ? comp : comp.id
          );
          return compIds.includes(componentName) || compIds.includes(`${section.id}_${componentName}`);
        })
        .map((section) => section.id);

  return sectionIds.map((sid) => ({
    componentName,
    sectionId: sid,
    compositionId: compToRemotionId(componentName, sid),
  }));
}

async function validatePreviewComposition(target: ValidationTarget): Promise<void> {
  const outputPath = path.join(
    os.tmpdir(),
    `composition-smoke-${target.compositionId}-${Date.now()}.png`,
  );

  try {
    await renderStill(target.compositionId, 30, outputPath);
  } finally {
    fs.rmSync(outputPath, { force: true });
  }
}

// ---------------------------------------------------------------------------
// Executor registration for compositions stage
// ---------------------------------------------------------------------------
registerExecutor("compositions", (params, send: SseSend) => {
  return async (onLog) => {
    const components = (params.components as string[]) ?? [];
    const wrappers = (params.wrappers as string[]) ?? [];
    const sectionId = params.sectionId as string | undefined;

    // Resolve section specDir for scoped spec lookup
    const sectionSpecDir = sectionId
        ? (() => {
            const cfg = loadProject();
            const sec = cfg.sections.find((s: { id: string }) => s.id === sectionId);
            return sec ? path.join("specs", sec.specDir) : undefined;
          })()
      : undefined;

    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;

    // Calculate section durations from audio files and update project.json
    // so that Root.tsx compositions have correct durationInFrames.
    const config = loadProject();
    const ttsOutputDir = path.join(getProjectDir(), "outputs", "tts");
    let durationsUpdated = false;
    for (const section of config.sections) {
      if (section.durationSeconds > 0) continue;
      const concatAudio = path.join(ttsOutputDir, section.id, "concatenated.wav");
      if (fs.existsSync(concatAudio)) {
        try {
          const result = execSync(
            `ffprobe -v error -show_entries format=duration -of default=noprint_wrappers=1:nokey=1 "${concatAudio}"`,
            { encoding: "utf-8" }
          );
          const duration = parseFloat(result.trim());
          if (!isNaN(duration) && duration > 0) {
            section.durationSeconds = duration;
            durationsUpdated = true;
            onLog(`[compositions] Section "${section.id}" duration: ${duration.toFixed(2)}s`);
          }
        } catch {
          onLog(`[compositions] Warning: could not get duration for ${section.id}`);
        }
      }
    }
    if (durationsUpdated) {
      // Recalculate offsets
      let offset = 0;
      for (const section of config.sections) {
        section.offsetSeconds = offset;
        offset += section.durationSeconds;
      }
      saveProject(config);
      onLog("[compositions] Updated project.json with audio durations.");
    }

    // Stage Veo assets BEFORE generating components so Claude knows which
    // video files are available and uses correct staticFile() paths.
    // Clean the target directory first to remove stale files from previous runs.
    const veoOutputDir = path.join(getProjectDir(), "outputs", "veo");
    const veoPublicDir = path.join(getAppRemotionPublicDir(), "veo");
    if (fs.existsSync(veoPublicDir)) {
      fs.rmSync(veoPublicDir, { recursive: true, force: true });
    }
    if (fs.existsSync(veoOutputDir)) {
      fs.mkdirSync(veoPublicDir, { recursive: true });
      for (const f of fs.readdirSync(veoOutputDir)) {
        if (f.endsWith(".mp4") || f.endsWith(".webm")) {
          fs.copyFileSync(
            path.join(veoOutputDir, f),
            path.join(veoPublicDir, f)
          );
        }
      }
      onLog("[compositions] Staged Veo assets to remotion/public/veo/");
    }

    const veoAssets = listVeoAssets();

    // Build a unified work list of { name, outputName, specDir } items.
    // When sectionComponents is provided (full run), each section's components
    // are generated with section-scoped filenames to avoid collisions.
    const sectionComponents = params.sectionComponents as SectionComponentEntry[] | undefined;

    type WorkItem = { name: string; outputName: string; specDir?: string; sectionId?: string };
    const workItems: WorkItem[] = [];

    if (sectionComponents && sectionComponents.length > 0) {
      const cfg = loadProject();
      for (const entry of sectionComponents) {
        const sec = cfg.sections.find((s: { id: string }) => s.id === entry.sectionId);
        const specDir = sec ? path.join("specs", sec.specDir) : undefined;
        for (const name of entry.components) {
          // Don't double-prefix if the name already starts with the sectionId
          const alreadyScoped = name.startsWith(`${entry.sectionId}_`);
          workItems.push({
            name,
            outputName: alreadyScoped ? name : `${entry.sectionId}_${name}`,
            specDir,
            sectionId: entry.sectionId,
          });
        }
      }
    } else {
      for (const name of components) {
        const alreadyScoped = sectionId && name.startsWith(`${sectionId}_`);
        workItems.push({
          name,
          outputName: alreadyScoped ? name : (sectionId ? `${sectionId}_${name}` : name),
          specDir: sectionSpecDir,
          sectionId,
        });
      }
    }

    const total = workItems.length + wrappers.length || 1;
    let completed = 0;
    const validatedItems: Array<{ name: string; sectionId?: string }> = [];

    // Generate components via Claude Code (or deterministic fallback for _main)
    // Wrap in try-finally so discovery always runs even if generation fails.
    // This ensures project.json is updated for components that succeeded.
    let generationError: Error | null = null;

    try {
      let nextWorkIndex = 0;
      const workerCount = workItems.length >= 4 ? 2 : 1;

      const runNextItem = async (): Promise<void> => {
        if (generationError) {
          return;
        }

        const currentIndex = nextWorkIndex++;
        if (currentIndex >= workItems.length) {
          return;
        }

        const item = workItems[currentIndex];
        send({ type: "component", name: item.name, status: "generating" });
        onLog(`[compositions] Generating component: ${item.outputName}`);

        try {
          if (isDeterministicPipelineMode()) {
            const spec = findSpecForComponent(item.name, item.specDir);
            writeDeterministicComponent(getRemotionScopeDir(), item.outputName, spec, onLog);
          } else if (item.name.endsWith("_main")) {
            const spec = findSpecForComponent(item.name, item.specDir);
            generateFallbackComponent(item.outputName, spec, veoAssets, onLog);
          } else {
            const spec = findSpecForComponent(item.name, item.specDir);
            const prompt = buildComponentPrompt(item.name, item.outputName, spec, veoAssets);
            await runClaudeFix(prompt, getRemotionScopeDir(), (line) => onLog(line));
          }

          send({ type: "component", name: item.name, status: "done" });
          validatedItems.push({ name: item.name, sectionId: item.sectionId });
        } catch (err) {
          const msg = err instanceof Error ? err.message : "Unknown error";
          send({ type: "component", name: item.name, status: "error" });
          onLog(`[compositions] Error generating ${item.name}: ${msg}`);
          generationError = err instanceof Error ? err : new Error(String(err));
          return;
        } finally {
          completed++;
          progressFn?.(Math.round((completed / total) * 100));
        }

        await runNextItem();
      };

      await Promise.all(
        Array.from({ length: workerCount }, () => runNextItem())
      );
    } catch (err) {
      generationError = err instanceof Error ? err : new Error(String(err));
    }

    // Discover generated components per section and populate compositions[]
    // in project.json so the Python wrapper script imports them.
    {
      const freshConfig = loadProject();
      let compositionsUpdated = false;

      for (const section of freshConfig.sections) {
        const sectionSpecDir = path.join(getSpecsDir(), section.specDir);
        if (!fs.existsSync(sectionSpecDir)) continue;

        const discoveredComponents: string[] = [];
        const specEntries = fs.readdirSync(sectionSpecDir, { withFileTypes: true });
        for (const entry of specEntries) {
          if (!entry.isFile()) continue;
          const base = path.basename(entry.name, path.extname(entry.name));
          // Skip spec.md (main section spec), AUDIT_ files, veo.json, and veo basename
          if (NON_COMPONENT_BASENAMES.has(base) || entry.name.startsWith("AUDIT_") || entry.name === "veo.json") continue;
          // Skip Veo generation prompts (first line contains [veo:])
          if (entry.name.endsWith(".md")) {
            try {
              const firstLine = fs.readFileSync(path.join(sectionSpecDir, entry.name), "utf-8").split("\n")[0];
              if (firstLine.includes("[veo:")) continue;
            } catch { /* ignore read errors */ }
          }
          // Check for component directory ({NN}-{PascalName}/index.ts), section-scoped file, or flat file
          const nnMatch = base.match(/^(\d{2})_/);
          const strippedPascal = nnMatch ? toPascalCase(base.slice(nnMatch[0].length)) : toPascalCase(base);
          const dirName = nnMatch ? `${nnMatch[1]}-${strippedPascal}` : strippedPascal;
          const dirIndex = path.join(getRemotionScopeDir(), dirName, "index.ts");
          const scopedTsx = path.join(getRemotionScopeDir(), `${section.id}_${base}.tsx`);
          const flatTsx = path.join(getRemotionScopeDir(), `${base}.tsx`);
          // Also check section-prefixed PascalCase directory (e.g., ColdOpen07MonitorGlowOverlay/)
          let pascalDirIndex: string | null = null;
          if (nnMatch) {
            const sectionPascal = toPascalCase(section.id);
            const fullPascal = `${sectionPascal}${nnMatch[1]}${strippedPascal}`;
            pascalDirIndex = path.join(getRemotionScopeDir(), fullPascal, "index.ts");
          }
          if (fs.existsSync(scopedTsx)) {
            discoveredComponents.push(`${section.id}_${base}`);
          } else if (fs.existsSync(flatTsx)) {
            discoveredComponents.push(base);
          } else if (fs.existsSync(dirIndex)) {
            discoveredComponents.push(base);
          } else if (pascalDirIndex && fs.existsSync(pascalDirIndex)) {
            discoveredComponents.push(base);
          }
        }

        // Fallback: if no individual component specs matched but Claude generated
        // the fallback {sectionId}_main.tsx component, discover it.
        if (discoveredComponents.length === 0) {
          const fallbackName = `${section.id}_main`;
          const fallbackTsx = path.join(getRemotionScopeDir(), `${fallbackName}.tsx`);
          if (fs.existsSync(fallbackTsx)) {
            discoveredComponents.push(fallbackName);
          }
        }

        if (discoveredComponents.length > 0) {
          // Merge: preserve existing timing data (startSeconds/durationSeconds) for known components
          const existingTimingMap = new Map<string, Exclude<SectionComposition, string>>();
          const existingComps: SectionComposition[] = section.compositions || [];
          for (const comp of existingComps) {
            if (typeof comp === "object" && comp !== null && comp.id) {
              existingTimingMap.set(comp.id, comp);
            }
          }
          const mergedCompositions: SectionComposition[] = [];
          for (const compId of discoveredComponents) {
            const existing = existingTimingMap.get(compId);
            mergedCompositions.push(existing ?? compId);
          }
          section.compositions = mergedCompositions;
          section.timelineSource =
            section.timelineSource === "generated" || !hasAuthoredSectionTimeline(section)
              ? "generated"
              : "authored";
          compositionsUpdated = true;
          onLog(`[compositions] Section "${section.id}" compositions: ${discoveredComponents.join(", ")}`);
        }
      }

      if (compositionsUpdated) {
        saveProject(freshConfig);
        onLog("[compositions] Updated project.json with discovered compositions.");
      }

      // Generate section constants and section composition for each section
      // that has discovered components (animation components → constants → composition)
      for (const section of freshConfig.sections) {
        if (!section.compositions || section.compositions.length === 0) continue;
        if (section.timelineSource !== "generated") {
          onLog(`[compositions] Preserving authored section timeline for ${section.id}.`);
          continue;
        }

        const sectionRemotionDir = path.join(getAppRemotionSrcDir(), section.id);
        // Extract string IDs from compositions (which may contain timing objects)
        const componentIds = (section.compositions as SectionComposition[]).map(
          (comp) => typeof comp === "string" ? comp : (comp.id as string)
        );
        try {
          if (isDeterministicPipelineMode()) {
            writeDeterministicSectionConstants(getProjectDir(), section, componentIds, onLog);
          } else {
            await generateSectionConstants(
              section,
              componentIds,
              sectionRemotionDir,
              onLog,
            );
          }
        } catch (err) {
          const msg = err instanceof Error ? err.message : "Unknown error";
          onLog(`[compositions] Warning: section constants/composition generation failed for ${section.id}: ${msg}`);
          // Non-fatal — the Python wrapper can still scaffold a basic composition
        }
      }
    }

    if (generationError) {
      onLog(
        "[compositions] Component generation had errors; continuing wrapper/root regeneration for successful components."
      );
    }

    // Always run the section compositions script to generate/update Root.tsx
    // and section wrapper components from project.json.
    if (wrappers.length > 0) {
      for (const name of wrappers) {
        send({ type: "component", name, status: "generating" });
      }
    }

    onLog("[compositions] Generating section compositions and Root.tsx...");
    await new Promise<void>((resolve, reject) => {
      const proc = spawn("python3", [
        path.join(getAppScriptsDir(), "generate_section_compositions.py"),
        "--project-dir",
        getProjectDir(),
        "--remotion-dir",
        getAppRemotionDir(),
        "--force",
      ], {
        cwd: getProjectDir(),
        stdio: ["ignore", "pipe", "pipe"],
      });

      proc.stdout.on("data", (d) => onLog(d.toString()));
      proc.stderr.on("data", (d) => onLog(d.toString()));

      proc.on("close", (code) => {
        if (code === 0) resolve();
        else reject(new Error(`Wrapper generation failed (code ${code})`));
      });
    });

    if (wrappers.length > 0) {
      for (const name of wrappers) {
        const filePath = path.join(getRemotionScopeDir(), `${name}.tsx`);
        if (fs.existsSync(filePath)) {
          send({ type: "component", name, status: "done" });
        } else {
          send({ type: "component", name, status: "error" });
        }
        completed++;
        progressFn?.(Math.round((completed / total) * 100));
      }
    }

    // Rebuild Remotion bundle so render stage uses fresh compositions
    onLog("[compositions] Rebuilding Remotion bundle...");
    send({ type: "bundle", status: "building" });

    const remotionDir = getAppRemotionDir();
    execSync("npx remotion bundle src/index.ts --out build", {
      cwd: remotionDir,
      stdio: "pipe",
      timeout: 120_000,
    });

    send({ type: "bundle", status: "done" });
    onLog("[compositions] Remotion bundle rebuilt.");

    const freshConfigForValidation = loadProject();
    const validationTargets = new Map<string, ValidationTarget>();
    for (const item of validatedItems) {
      const targets = resolveValidationTargets(
        item.name,
        item.sectionId,
        freshConfigForValidation.sections,
      );
      for (const target of targets) {
        validationTargets.set(`${target.sectionId}:${target.componentName}`, target);
      }
    }

    const validationFailures: string[] = [];
    if (shouldSkipPreviewValidation()) {
      onLog("[compositions] Skipping preview validation (VIDEO_EDITOR_SKIP_COMPOSITION_VALIDATION=1).");
    } else {
      for (const target of validationTargets.values()) {
        try {
          onLog(
            `[compositions] Validating preview composition: ${target.componentName} (${target.compositionId})`
          );
          await validatePreviewComposition(target);
        } catch (err) {
          const msg = err instanceof Error ? err.message : "Unknown validation error";
          validationFailures.push(`${target.componentName}: ${msg}`);
          send({ type: "component", name: target.componentName, status: "error" });
          onLog(
            `[compositions] Validation failed for ${target.componentName}: ${msg}`
          );
        }
      }
    }

    if (validationFailures.length > 0 && !generationError) {
      generationError = new Error(
        `Component validation failed: ${validationFailures.join("; ")}`
      );
    }

    if (generationError) {
      throw generationError;
    }
  };
});

// ---------------------------------------------------------------------------
// Route handler: POST /api/pipeline/compositions/run
// ---------------------------------------------------------------------------
export async function POST(request: NextRequest): Promise<Response> {
  const body = (await request.json()) as RunBody;
  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage("compositions", body, send);
      send({ type: "complete", jobId });
      done();
    } catch (err) {
      const msg = err instanceof Error ? err.message : "Unknown error";
      error(msg);
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
