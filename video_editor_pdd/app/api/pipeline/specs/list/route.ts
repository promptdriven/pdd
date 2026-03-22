import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

import { loadProject } from "@/lib/project";
import { getProjectDir } from "@/lib/projects";

/**
 * GET /api/pipeline/specs/list
 *
 * Reads the project sections from project.json and scans the specs/ directory
 * for each section's specDir. Returns sections with file metadata including
 * existence and first-line content (used for type badges like [Remotion], [veo:]).
 */

interface SpecFile {
  path: string;
  exists: boolean;
  firstLine?: string;
  parentSpec?: string;
}

interface SpecSection {
  id: string;
  label: string;
  files: SpecFile[];
}

function normalizeRelativeSpecDir(specDir: string): string {
  return specDir.replace(/^specs[\\/]/, "").replace(/\\/g, "/");
}

function resolveSpecDirPaths(specDir: string, specsRoot: string): {
  abs: string;
  rel: string;
} {
  const abs = path.isAbsolute(specDir)
    ? specDir
    : path.join(specsRoot, normalizeRelativeSpecDir(specDir));

  const relativeFromRoot = path.relative(specsRoot, abs).replace(/\\/g, "/");
  const relDir = relativeFromRoot.startsWith("..")
    ? normalizeRelativeSpecDir(specDir)
    : relativeFromRoot;

  return {
    abs,
    rel: path.posix.join("specs", relDir),
  };
}

function readFirstLine(filePath: string): string | undefined {
  try {
    const content = fs.readFileSync(filePath, "utf-8");
    const firstLine = content.split("\n")[0]?.trim();
    return firstLine || undefined;
  } catch {
    return undefined;
  }
}

function listSpecFiles(specDirAbs: string, specDirRel: string): SpecFile[] {
  if (!fs.existsSync(specDirAbs)) {
    return [];
  }

  const entries = fs.readdirSync(specDirAbs, { withFileTypes: true });
  const files: SpecFile[] = [];

  for (const entry of entries) {
    if (!entry.isFile()) continue;
    if (!entry.name.endsWith(".md") && !entry.name.endsWith(".txt")) continue;
    if (entry.name.startsWith("AUDIT_")) continue;

    const absPath = path.join(specDirAbs, entry.name);
    const relPath = path.join(specDirRel, entry.name);

    files.push({
      path: relPath,
      exists: true,
      firstLine: readFirstLine(absPath),
    });
  }

  return files;
}

const DATA_POINTS_JSON_RE = /(?:^|\n)##\s*Data Points(?:\s+JSON)?\s*(?:\r?\n)+```json\s*([\s\S]+?)\s*```/i;
const SPLIT_MARKER_RE = /^\s*\[split:[^\]]*\]/i;

function extractChildClipIds(content: string): string[] {
  if (!SPLIT_MARKER_RE.test(content)) {
    return [];
  }

  const match = DATA_POINTS_JSON_RE.exec(content);
  if (!match?.[1]) {
    return [];
  }

  let dataPoints: Record<string, unknown>;
  try {
    dataPoints = JSON.parse(match[1]);
  } catch {
    return [];
  }

  const ids: string[] = [];

  function collect(value: unknown): void {
    if (typeof value === "string" && value.trim()) {
      ids.push(value.trim());
    } else if (value && typeof value === "object" && !Array.isArray(value)) {
      for (const [key, nested] of Object.entries(value as Record<string, unknown>)) {
        const normalized = key.replace(/[_-]/g, "").toLowerCase();
        if (
          (normalized === "leftclipid" || normalized === "rightclipid" ||
           normalized === "clipid" || normalized === "content") &&
          typeof nested === "string" && nested.trim()
        ) {
          ids.push(nested.trim());
        } else if (typeof nested === "object" && nested !== null) {
          collect(nested);
        }
      }
    }
  }

  collect(dataPoints);
  return ids;
}

function resolveParentSpecs(files: SpecFile[], specDirAbs: string): void {
  const containerChildren = new Map<string, string[]>();

  for (const file of files) {
    const fileName = path.basename(file.path);
    const absPath = path.join(specDirAbs, fileName);
    if (!file.exists) continue;

    let content: string;
    try {
      content = fs.readFileSync(absPath, "utf-8");
    } catch {
      continue;
    }

    const childIds = extractChildClipIds(content);
    if (childIds.length > 0) {
      containerChildren.set(fileName, childIds);
    }
  }

  if (containerChildren.size === 0) return;

  for (const file of files) {
    const fileName = path.basename(file.path);
    const baseName = fileName.replace(/\.md$/, "");
    const stripped = baseName.replace(/^\d+_/, "");

    for (const [containerName, childIds] of containerChildren) {
      if (fileName === containerName) continue;

      const matched = childIds.some((id) => {
        const normalizedId = id.replace(/[_-]/g, "").toLowerCase();
        const normalizedBase = baseName.replace(/[_-]/g, "").toLowerCase();
        const normalizedStripped = stripped.replace(/[_-]/g, "").toLowerCase();
        return (
          normalizedBase === normalizedId ||
          normalizedStripped === normalizedId ||
          normalizedBase.includes(normalizedId) ||
          normalizedStripped.includes(normalizedId)
        );
      });

      if (matched) {
        file.parentSpec = containerName;
        break;
      }
    }
  }
}

export async function GET(): Promise<NextResponse> {
  try {
    const config = loadProject();
    const specsRoot = path.join(getProjectDir(), "specs");
    const sections: SpecSection[] = [];

    for (const section of config.sections) {
      const { rel: specDirRel, abs: specDirAbs } = resolveSpecDirPaths(
        section.specDir,
        specsRoot
      );

      const files = listSpecFiles(specDirAbs, specDirRel);
      resolveParentSpecs(files, specDirAbs);

      // If no files exist yet, add a placeholder entry for the expected spec
      if (files.length === 0) {
        files.push({
          path: path.join(specDirRel, "spec.md"),
          exists: false,
        });
      }

      sections.push({
        id: section.id,
        label: section.label,
        files,
      });
    }

    return NextResponse.json({ sections });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message, sections: [] },
      { status: 500 }
    );
  }
}
