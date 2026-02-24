import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

import { loadProject } from "@/lib/project";

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
}

interface SpecSection {
  id: string;
  label: string;
  files: SpecFile[];
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

export async function GET(): Promise<NextResponse> {
  try {
    const config = loadProject();
    const specsRoot = path.join(process.cwd(), "specs");
    const sections: SpecSection[] = [];

    for (const section of config.sections) {
      const specDirRel = path.join("specs", section.specDir);
      const specDirAbs = path.join(specsRoot, section.specDir);

      const files = listSpecFiles(specDirAbs, specDirRel);

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
