import { NextRequest } from "next/server";
import path from "path";
import fs from "fs";
import { spawn, execSync } from "child_process";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { createSseStream } from "@/lib/sse";
import { runClaudeFix } from "@/lib/claude";
import { loadProject, saveProject } from "@/lib/project";
import type { SseSend } from "@/lib/types";

type RunBody = {
  components?: string[];
  wrappers?: string[];
  sectionId?: string;
};

const REMOTION_SCOPE_DIR = path.join(process.cwd(), "remotion/src/remotion");
const SPECS_DIR = path.join(process.cwd(), "specs");

/** Names that are section-level metadata, not visual components. */
const NON_COMPONENT_BASENAMES = new Set(["spec", "veo"]);

// ---------------------------------------------------------------------------
// Utility: find spec file content for a component (best effort)
// ---------------------------------------------------------------------------
function findSpecForComponent(componentName: string, sectionSpecDir?: string): string {
  if (!fs.existsSync(SPECS_DIR)) return "";

  // When a section specDir is provided, search there first for an exact match
  if (sectionSpecDir) {
    const absDir = path.isAbsolute(sectionSpecDir)
      ? sectionSpecDir
      : path.join(process.cwd(), sectionSpecDir);
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
    const specMd = path.join(SPECS_DIR, sectionId, "spec.md");
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

  walk(SPECS_DIR);

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
  const veoPublicDir = path.join(process.cwd(), "remotion", "public", "veo");
  if (!fs.existsSync(veoPublicDir)) return [];
  return fs.readdirSync(veoPublicDir).filter((f) => f.endsWith(".mp4") || f.endsWith(".webm"));
}

function buildComponentPrompt(name: string, spec: string, veoAssets: string[]): string {
  const veoSection = veoAssets.length > 0
    ? `\n--- VEO ASSETS ---\nThe following video files are available in remotion/public/veo/.\nUse staticFile("veo/<filename>") to reference them (NOT staticFile("public/veo/...")).\n${veoAssets.map((f) => `- ${f}`).join("\n")}\n--- END VEO ASSETS ---\n`
    : "";

  const exportName = toPascalCase(name);

  return `
You are Claude Code. Generate a Remotion component.

Component name: ${name}
Target directory: remotion/src/remotion/
Output file: remotion/src/remotion/${name}.tsx

CRITICAL EXPORT REQUIREMENT:
- The component MUST be exported as BOTH a named export AND a default export with EXACTLY this name: ${exportName}
- Example: export const ${exportName}: React.FC = () => { ... }; export default ${exportName};
- Do NOT use any other name for the export.

CRITICAL RENDERING REQUIREMENTS:
- The component MUST render visible content from frame 0 (no delayed fade-ins).
- Use an <AbsoluteFill> with a non-black background color (e.g., "#0A1628" dark navy).
- All animated elements must use bright, high-contrast colors (e.g., white, bright blue #3B82F6, green #22C55E).
- Every visual element must have explicit width, height, and position.
- Do NOT import external data files (e.g., JSON word timestamps) that may not exist.
  If subtitles are needed, embed word data inline or skip subtitles.
- Only import from "remotion" — do not import from other local files unless they are guaranteed to exist.

Use the spec below to implement the component accurately.

--- SPEC ---
${spec || "(spec not found, infer from naming)"}
--- END SPEC ---
${veoSection}
Return valid TypeScript/React code.
`;
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
  const outPath = path.join(REMOTION_SCOPE_DIR, `${name}.tsx`);

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
    const ttsOutputDir = path.join(process.cwd(), "outputs", "tts");
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
    const veoOutputDir = path.join(process.cwd(), "outputs", "veo");
    const veoPublicDir = path.join(process.cwd(), "remotion", "public", "veo");
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

    const total = components.length + wrappers.length || 1;
    let completed = 0;

    // Generate components via Claude Code (or deterministic fallback for _main)
    for (const name of components) {
      // When sectionId is provided, scope output filename to avoid collisions
      const outputName = sectionId ? `${sectionId}_${name}` : name;

      send({ type: "component", name, status: "generating" });
      onLog(`[compositions] Generating component: ${outputName}`);

      try {
        if (name.endsWith("_main")) {
          // Use deterministic template for fallback components to avoid
          // non-deterministic Claude output that may render all-black.
          const spec = findSpecForComponent(name, sectionSpecDir);
          generateFallbackComponent(outputName, spec, veoAssets, onLog);
        } else {
          const spec = findSpecForComponent(name, sectionSpecDir);
          const prompt = buildComponentPrompt(outputName, spec, veoAssets);
          await runClaudeFix(prompt, REMOTION_SCOPE_DIR, (line) => onLog(line));
        }

        send({ type: "component", name, status: "done" });
      } catch (err) {
        const msg = err instanceof Error ? err.message : "Unknown error";
        send({ type: "component", name, status: "error" });
        onLog(`[compositions] Error generating ${name}: ${msg}`);
        throw err;
      } finally {
        completed++;
        progressFn?.(Math.round((completed / total) * 100));
      }
    }

    // Discover generated components per section and populate compositions[]
    // in project.json so the Python wrapper script imports them.
    {
      const freshConfig = loadProject();
      let compositionsUpdated = false;

      for (const section of freshConfig.sections) {
        const sectionSpecDir = path.join(SPECS_DIR, section.specDir);
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
          // Check for section-scoped file first ({sectionId}_{base}.tsx), then flat ({base}.tsx)
          const scopedTsx = path.join(REMOTION_SCOPE_DIR, `${section.id}_${base}.tsx`);
          const flatTsx = path.join(REMOTION_SCOPE_DIR, `${base}.tsx`);
          if (fs.existsSync(scopedTsx)) {
            discoveredComponents.push(`${section.id}_${base}`);
          } else if (fs.existsSync(flatTsx)) {
            discoveredComponents.push(base);
          }
        }

        // Fallback: if no individual component specs matched but Claude generated
        // the fallback {sectionId}_main.tsx component, discover it.
        if (discoveredComponents.length === 0) {
          const fallbackName = `${section.id}_main`;
          const fallbackTsx = path.join(REMOTION_SCOPE_DIR, `${fallbackName}.tsx`);
          if (fs.existsSync(fallbackTsx)) {
            discoveredComponents.push(fallbackName);
          }
        }

        if (discoveredComponents.length > 0) {
          section.compositions = discoveredComponents;
          compositionsUpdated = true;
          onLog(`[compositions] Section "${section.id}" compositions: ${discoveredComponents.join(", ")}`);
        }
      }

      if (compositionsUpdated) {
        saveProject(freshConfig);
        onLog("[compositions] Updated project.json with discovered compositions.");
      }
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
      const proc = spawn("python3", ["scripts/generate_section_compositions.py", "--force"], {
        cwd: process.cwd(),
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
        const filePath = path.join(REMOTION_SCOPE_DIR, `${name}.tsx`);
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

    const remotionDir = path.join(process.cwd(), "remotion");
    execSync("npx remotion bundle src/index.ts --out build", {
      cwd: remotionDir,
      stdio: "pipe",
      timeout: 120_000,
    });

    send({ type: "bundle", status: "done" });
    onLog("[compositions] Remotion bundle rebuilt.");
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

