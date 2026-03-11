import fs from "fs";
import path from "path";
import { execFileSync } from "child_process";

import { buildSectionConstantsSource } from "./composition-timing";
import type { Section } from "./types";

const DEFAULT_FPS = 30;

type SectionLike = Pick<Section, "id" | "label" | "specDir" | "durationSeconds" | "compositionId">;

function ensureDir(dirPath: string): void {
  fs.mkdirSync(dirPath, { recursive: true });
}

function collectFilesRecursively(rootDir: string, predicate: (filePath: string) => boolean): string[] {
  if (!fs.existsSync(rootDir)) {
    return [];
  }

  const results: string[] = [];

  for (const entry of fs.readdirSync(rootDir, { withFileTypes: true })) {
    const entryPath = path.join(rootDir, entry.name);
    if (entry.isDirectory()) {
      results.push(...collectFilesRecursively(entryPath, predicate));
      continue;
    }

    if (predicate(entryPath)) {
      results.push(entryPath);
    }
  }

  return results;
}

function cleanText(value: string): string {
  return value.replace(/\s+/g, " ").trim();
}

function toPascalCase(value: string): string {
  return value
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0]?.toUpperCase() + part.slice(1))
    .join("");
}

function titleFromId(sectionId: string): string {
  return sectionId
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0]?.toUpperCase() + part.slice(1))
    .join(" ");
}

function defaultSectionNarration(section: Pick<SectionLike, "id" | "label">): string[] {
  const title = section.label || titleFromId(section.id);
  return [
    `This section introduces ${title} in a deterministic test render.`,
    `The visuals stay simple so the pipeline can verify timing, audio sync, and final stitching.`,
  ];
}

function extractSectionsFromMainScript(mainScript: string): Array<{ heading: string; narration: string[] }> {
  const headingMatches = Array.from(mainScript.matchAll(/^##\s+(.+?)\s*$/gm));

  return headingMatches
    .map((match, index) => {
      const heading = cleanText(match[1] ?? "");
      const start = match.index ?? 0;
      const bodyStart = start + match[0].length;
      const bodyEnd = headingMatches[index + 1]?.index ?? mainScript.length;
      const body = mainScript.slice(bodyStart, bodyEnd);
      const narration = Array.from(
        body.matchAll(/\*\*NARRATOR:\*\*\s*([\s\S]*?)(?=\n\s*\*\*\[VISUAL:|\n\s*---|\n\s*\*\*NARRATOR:\*\*|\n##\s+|$)/g),
      )
        .map((narrationMatch) => cleanText(narrationMatch[1] ?? ""))
        .filter(Boolean);

      return { heading, narration };
    })
    .filter((section) => section.heading.length > 0);
}

export function isDeterministicPipelineMode(): boolean {
  return process.env.PDD_DETERMINISTIC_PIPELINE === "1";
}

export function buildDeterministicTtsScript(
  mainScript: string,
  sections: ReadonlyArray<Pick<SectionLike, "id" | "label">>,
): string {
  const extracted = extractSectionsFromMainScript(mainScript);
  const byHeading = new Map<string, string[]>();

  for (const section of extracted) {
    byHeading.set(section.heading.toLowerCase(), section.narration);
  }

  const blocks = sections.map((section) => {
    const heading = section.label || titleFromId(section.id);
    const directMatch = byHeading.get(heading.toLowerCase());
    const inferredMatch = extracted.find(
      (candidate) => candidate.heading.toLowerCase().includes(section.id.replace(/_/g, " ")),
    )?.narration;
    const narration =
      (directMatch && directMatch.length > 0 ? directMatch : undefined) ??
      (inferredMatch && inferredMatch.length > 0 ? inferredMatch : undefined) ??
      defaultSectionNarration(section);

    const lines = [
      `## ${heading}`,
      "",
    ];

    narration.forEach((paragraph, index) => {
      lines.push("[TONE: explanatory]");
      lines.push("[PACE: moderate]");
      lines.push("[EMOTION: calm]");
      lines.push(paragraph);
      if (index < narration.length - 1) {
        lines.push("[PAUSE: 1.0s]");
      }
      lines.push("");
    });

    return lines.join("\n").trimEnd();
  });

  return `${blocks.join("\n\n---\n\n")}\n`;
}

export function writeDeterministicTtsScript(
  projectDir: string,
  sections: ReadonlyArray<Pick<SectionLike, "id" | "label">>,
  onLog?: (message: string) => void,
): string {
  const narrativeDir = path.join(projectDir, "narrative");
  const mainScriptPath = path.join(narrativeDir, "main_script.md");
  const ttsScriptPath = path.join(narrativeDir, "tts_script.md");
  const mainScript = fs.existsSync(mainScriptPath)
    ? fs.readFileSync(mainScriptPath, "utf-8")
    : "";
  const content = buildDeterministicTtsScript(mainScript, sections);

  ensureDir(narrativeDir);
  fs.writeFileSync(ttsScriptPath, content);
  onLog?.(`[tts-script] Wrote deterministic script: ${path.relative(projectDir, ttsScriptPath)}`);

  return ttsScriptPath;
}

function buildSpecTemplate(
  marker: string,
  heading: string,
  summary: string,
  tool: string,
  durationSeconds: number,
): string {
  return [
    marker,
    `# ${heading}`,
    "",
    `**Tool:** ${tool}`,
    `**Duration:** ~${durationSeconds}s`,
    "**Timestamp:** 0:00 - 0:05",
    "",
    "## Visual Description",
    summary,
    "",
    "## Technical Specifications",
    "",
    "### Canvas",
    "- Resolution: 1920x1080 (16:9)",
    "- Background: #0A1628",
    "",
    "### Animation Sequence",
    "1. Frame 0-30: Establish the composition immediately.",
    "2. Frame 30-90: Introduce the main motion or layout change.",
    "3. Frame 90-150: Hold the final state clearly for rendering verification.",
    "",
    "## Narration Sync",
    `> "${summary}"`,
    "",
    "## Code Structure (Remotion)",
    "```typescript",
    "<Sequence from={0} durationInFrames={150}>",
    "  <AbsoluteFill />",
    "</Sequence>",
    "```",
    "",
    "## Data Points",
    "```json",
    '{"series":[{"label":"A","value":1},{"label":"B","value":2}]}',
    "```",
    "",
  ].join("\n");
}

function defaultVeoPrompts(section: Pick<SectionLike, "id" | "label">): [string, string] {
  const label = section.label || titleFromId(section.id);
  return [
    `A cinematic establishing shot for ${label}, soft natural light, steady camera motion, crisp detail`,
    `A complementary cinematic cutaway for ${label}, gentle movement, rich contrast, polished editorial look`,
  ];
}

export function writeDeterministicSpecsForSection(
  projectDir: string,
  section: Pick<SectionLike, "id" | "label" | "specDir">,
  onLog?: (message: string) => void,
): string[] {
  const specDir = path.join(projectDir, "specs", section.specDir);
  const label = section.label || titleFromId(section.id);
  const [veoPromptA, veoPromptB] = defaultVeoPrompts(section);

  ensureDir(specDir);

  const files = [
    {
      name: "01_title_card.md",
      content: buildSpecTemplate(
        "[title:]",
        `${label} Title Card`,
        `${label} appears as a crisp title card with immediate readability.`,
        "Remotion",
        4,
      ),
    },
    {
      name: "02_key_visual.md",
      content: buildSpecTemplate(
        "[Remotion]",
        `${label} Key Visual`,
        `${label} is represented by a simple animated chart with strong contrast and visible motion.`,
        "Remotion",
        5,
      ),
    },
    {
      name: "03_split_summary.md",
      content: buildSpecTemplate(
        "[split:]",
        `${label} Split Summary`,
        `${label} is explained through a balanced split-screen comparison.`,
        "Remotion",
        5,
      ),
    },
    {
      name: "04_veo_broll.md",
      content: buildSpecTemplate(
        `[veo: ${veoPromptA}]`,
        `${label} Veo B-Roll`,
        `${label} receives a cinematic supporting shot for downstream Veo generation.`,
        "Veo",
        4,
      ),
    },
    {
      name: "05_veo_cutaway.md",
      content: buildSpecTemplate(
        `[veo: ${veoPromptB}]`,
        `${label} Veo Cutaway`,
        `${label} receives a second cinematic cutaway for downstream Veo generation.`,
        "Veo",
        4,
      ),
    },
  ];

  for (const file of files) {
    fs.writeFileSync(path.join(specDir, file.name), file.content);
  }

  const veoJsonPath = path.join(specDir, "veo.json");
  if (!fs.existsSync(veoJsonPath)) {
    fs.writeFileSync(veoJsonPath, JSON.stringify({ prompt: veoPromptA }, null, 2));
  }

  onLog?.(`[specs] Wrote deterministic specs for ${section.id}`);

  return files.map((file) => path.join(specDir, file.name));
}

function extractSpecMarker(specContent: string): string {
  return specContent.split("\n")[0]?.trim().toLowerCase() ?? "";
}

function buildTitleCardComponent(exportName: string, label: string): string {
  return `import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";

export const ${exportName}: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, 18, 120], [0, 1, 1], { extrapolateRight: "clamp" });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#0A1628",
        justifyContent: "center",
        alignItems: "center",
        color: "#F8FAFC",
        fontFamily: "sans-serif",
      }}
    >
      <div style={{ opacity, textAlign: "center" }}>
        <div style={{ fontSize: 24, letterSpacing: 6, textTransform: "uppercase", color: "#38BDF8" }}>
          Deterministic Render
        </div>
        <div style={{ fontSize: 72, fontWeight: 700, marginTop: 24 }}>
          ${label}
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default ${exportName};
`;
}

function buildSplitComponent(exportName: string, label: string): string {
  return `import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";

export const ${exportName}: React.FC = () => {
  const frame = useCurrentFrame();
  const dividerX = interpolate(frame, [0, 90], [640, 720], { extrapolateRight: "clamp" });

  return (
    <AbsoluteFill style={{ backgroundColor: "#020617", fontFamily: "sans-serif", color: "#E2E8F0" }}>
      <div style={{ position: "absolute", inset: 0, display: "flex" }}>
        <div style={{ flex: 1, backgroundColor: "#0F172A", display: "flex", justifyContent: "center", alignItems: "center" }}>
          <div style={{ fontSize: 46, fontWeight: 700 }}>Before</div>
        </div>
        <div style={{ flex: 1, backgroundColor: "#111827", display: "flex", justifyContent: "center", alignItems: "center" }}>
          <div style={{ fontSize: 46, fontWeight: 700 }}>After</div>
        </div>
      </div>
      <div style={{ position: "absolute", top: 0, bottom: 0, left: dividerX, width: 6, backgroundColor: "#38BDF8" }} />
      <div style={{ position: "absolute", top: 64, left: 64, fontSize: 54, fontWeight: 700 }}>
        ${label}
      </div>
    </AbsoluteFill>
  );
};

export default ${exportName};
`;
}

function buildChartComponent(exportName: string, label: string): string {
  return `import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";

const BARS = [0.35, 0.55, 0.8, 0.6];

export const ${exportName}: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628", justifyContent: "center", alignItems: "center", fontFamily: "sans-serif" }}>
      <div style={{ position: "absolute", top: 72, left: 72, color: "#F8FAFC", fontSize: 52, fontWeight: 700 }}>
        ${label}
      </div>
      <div style={{ display: "flex", gap: 36, alignItems: "flex-end", height: 420 }}>
        {BARS.map((value, index) => {
          const scale = interpolate(frame, [0, 20 + index * 10, 90 + index * 10], [0, value, value], { extrapolateRight: "clamp" });
          return (
            <div
              key={index}
              style={{
                width: 120,
                height: 360 * scale,
                borderRadius: 24,
                background: index % 2 === 0 ? "#38BDF8" : "#22C55E",
                boxShadow: "0 12px 40px rgba(15, 23, 42, 0.45)",
              }}
            />
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

export default ${exportName};
`;
}

export function writeDeterministicComponent(
  remotionScopeDir: string,
  outputName: string,
  specContent: string,
  onLog?: (message: string) => void,
): string {
  const exportName = toPascalCase(outputName);
  const label = titleFromId(outputName.replace(/^\w+_0\d_/, ""));
  const marker = extractSpecMarker(specContent);
  const outPath = path.join(remotionScopeDir, `${outputName}.tsx`);

  let source = buildChartComponent(exportName, label);
  if (marker.startsWith("[title:")) {
    source = buildTitleCardComponent(exportName, label);
  } else if (marker.startsWith("[split:")) {
    source = buildSplitComponent(exportName, label);
  }

  ensureDir(path.dirname(outPath));
  fs.writeFileSync(outPath, source);
  onLog?.(`[compositions] Wrote deterministic component: ${outputName}`);

  return outPath;
}

export function writeDeterministicSectionConstants(
  projectDir: string,
  section: Pick<SectionLike, "id" | "specDir" | "compositionId" | "durationSeconds">,
  componentIds: string[],
  onLog?: (message: string) => void,
): string {
  const outDir = path.join(projectDir, "remotion", "src", "remotion", section.id);
  const outPath = path.join(outDir, "constants.ts");
  const source = buildSectionConstantsSource(projectDir, section, componentIds, DEFAULT_FPS);

  ensureDir(outDir);
  fs.writeFileSync(outPath, source);
  onLog?.(`[compositions] Wrote deterministic constants: remotion/src/remotion/${section.id}/constants.ts`);

  return outPath;
}

function replaceBackgroundColorLiterals(source: string, color: string): string {
  return source
    .replace(/(backgroundColor\s*:\s*["'])#[0-9A-Fa-f]{3,6}(["'])/g, `$1${color}$2`)
    .replace(/(background\s*:\s*["'])#[0-9A-Fa-f]{3,6}(["'])/g, `$1${color}$2`);
}

export function applyDeterministicRemotionFix(
  projectDir: string,
  sectionId: string,
  instructionText: string,
  onLog?: (message: string) => void,
): string[] {
  const requestedColor = extractRequestedHexColor(instructionText);
  const remotionDir = path.join(projectDir, "remotion", "src", "remotion");
  const modifiedFiles: string[] = [];
  const sectionPascal = toPascalCase(sectionId);

  if (!fs.existsSync(remotionDir)) {
    return modifiedFiles;
  }

  const candidateFiles = collectFilesRecursively(remotionDir, (filePath) => {
    if (!/\.(tsx|ts)$/.test(filePath)) {
      return false;
    }

    const relativePath = path.relative(remotionDir, filePath).replace(/\\/g, "/");
    const baseName = path.basename(filePath);

    return (
      relativePath.startsWith(`${sectionId}/`) ||
      baseName.startsWith(`${sectionId}_`) ||
      baseName.startsWith(sectionPascal) ||
      relativePath.startsWith(`${sectionPascal}/`)
    );
  });

  for (const filePath of candidateFiles) {
    const original = fs.readFileSync(filePath, "utf-8");
    const updated = replaceBackgroundColorLiterals(original, requestedColor);
    if (updated !== original) {
      fs.writeFileSync(filePath, updated);
      modifiedFiles.push(filePath);
      onLog?.(`[resolve-batch] Applied deterministic fix: ${path.relative(projectDir, filePath)}`);
    }
  }

  return modifiedFiles;
}

export function extractRequestedHexColor(instructionText: string): string {
  return instructionText.match(/#(?:[0-9A-Fa-f]{6}|[0-9A-Fa-f]{3})\b/)?.[0]?.toUpperCase() ?? "#FF0000";
}

export function applyDeterministicVideoOverlay(
  videoPath: string,
  color: string,
  onLog?: (message: string) => void,
): void {
  const parsedColor = color.replace(/^#/, "");
  const tempPath = videoPath.replace(/\.mp4$/i, `.${Date.now()}.tmp.mp4`);

  execFileSync(
    "ffmpeg",
    [
      "-y",
      "-i",
      videoPath,
      "-map",
      "0",
      "-vf",
      `drawbox=x=0:y=0:w=iw:h=ih:color=0x${parsedColor}@0.35:t=fill`,
      "-c:v",
      "libx264",
      "-pix_fmt",
      "yuv420p",
      "-c:a",
      "copy",
      tempPath,
    ],
    { stdio: "pipe" },
  );

  fs.renameSync(tempPath, videoPath);
  onLog?.(`[resolve-batch] Applied deterministic video overlay: ${videoPath}`);
}

export function generateDeterministicVeoClip(
  outputPath: string,
  onLog?: (message: string) => void,
): void {
  ensureDir(path.dirname(outputPath));

  execFileSync(
    "ffmpeg",
    [
      "-y",
      "-f",
      "lavfi",
      "-i",
      "testsrc2=size=1280x720:rate=30",
      "-t",
      "4",
      "-pix_fmt",
      "yuv420p",
      outputPath,
    ],
    { stdio: "pipe" },
  );

  onLog?.(`[veo] Wrote deterministic clip: ${outputPath}`);
}
