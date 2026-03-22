import fs from "fs";
import path from "path";

import { parseSpecTimestampRange } from "./spec-timestamp";
import type { Annotation, Section } from "./types";

type SpecPatch = {
  specPath: string;
  note: string;
};

const getTimestampWindow = (content: string): { start: number; end: number } | null => {
  const range = parseSpecTimestampRange(content);
  if (!range) {
    return null;
  }

  return {
    start: range.startSeconds,
    end: range.endSeconds,
  };
};

const resolveSpecDir = (projectDir: string, specDir: string): string => {
  if (path.isAbsolute(specDir)) {
    return specDir;
  }

  const normalized = specDir.replace(/^specs[\\/]/, "");
  return path.join(projectDir, "specs", normalized);
};

const buildAnnotationBlock = (annotation: Annotation): string => {
  const startMarker = `<!-- ANNOTATION_UPDATE_START: ${annotation.id} -->`;
  const endMarker = `<!-- ANNOTATION_UPDATE_END: ${annotation.id} -->`;
  const suggestedFixes = annotation.analysis?.suggestedFixes ?? [];

  return [
    startMarker,
    "## Annotation Update",
    `Requested change: ${annotation.text}`,
    `Technical assessment: ${annotation.analysis?.technicalAssessment ?? "None provided."}`,
    ...suggestedFixes.map((fix) => `- ${fix}`),
    endMarker,
  ].join("\n");
};

export function applyRemotionSpecFixForAnnotation(
  projectDir: string,
  section: Section,
  annotation: Annotation,
): SpecPatch | null {
  const specDir = resolveSpecDir(projectDir, section.specDir);
  if (!fs.existsSync(specDir)) {
    return null;
  }

  const specFiles = fs
    .readdirSync(specDir)
    .filter((entry) => entry.endsWith(".md") && !entry.startsWith("AUDIT_"))
    .sort();

  let targetPath: string | null = null;
  for (const entry of specFiles) {
    const absPath = path.join(specDir, entry);
    const content = fs.readFileSync(absPath, "utf-8");
    const window = getTimestampWindow(content);
    if (
      window &&
      annotation.timestamp != null &&
      annotation.timestamp >= window.start &&
      annotation.timestamp < window.end
    ) {
      targetPath = absPath;
      break;
    }
  }

  if (!targetPath && specFiles.length > 0) {
    targetPath = path.join(specDir, specFiles[0]);
  }

  if (!targetPath) {
    return null;
  }

  const content = fs.readFileSync(targetPath, "utf-8");
  const startMarker = `<!-- ANNOTATION_UPDATE_START: ${annotation.id} -->`;
  const endMarker = `<!-- ANNOTATION_UPDATE_END: ${annotation.id} -->`;
  const block = buildAnnotationBlock(annotation);
  const markerRe = new RegExp(
    `${startMarker.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}[\\s\\S]*?${endMarker.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`,
    "m",
  );

  const updated = markerRe.test(content)
    ? content.replace(markerRe, block)
    : `${content.trimEnd()}\n\n${block}\n`;

  fs.writeFileSync(targetPath, updated, "utf-8");
  return { specPath: targetPath, note: annotation.text };
}
