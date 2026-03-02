import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

import { loadProject } from "@/lib/project";

/**
 * GET /api/pipeline/compositions/list
 *
 * Returns composition sections with their components and wrappers,
 * including generation status derived from the file system.
 */

type ComponentStatus = "done" | "missing" | "error" | "pending";

interface CompositionComponent {
  name: string;
  status: ComponentStatus;
  error?: string | null;
}

interface CompositionSection {
  id: string;
  label: string;
  components: CompositionComponent[];
  wrappers: CompositionComponent[];
}

const REMOTION_DIR = path.join(process.cwd(), "remotion", "src", "remotion");
const SPECS_DIR = path.join(process.cwd(), "specs");

/** Check if a spec file is a Veo generation prompt (not a Remotion component). */
function isVeoPromptSpec(filePath: string): boolean {
  try {
    const fd = fs.openSync(filePath, "r");
    const buf = Buffer.alloc(128);
    fs.readSync(fd, buf, 0, 128, 0);
    fs.closeSync(fd);
    const firstLine = buf.toString("utf-8").split("\n")[0];
    return firstLine.includes("[veo:") || firstLine.includes("[veo ]");
  } catch {
    return false;
  }
}

/**
 * List Remotion component spec files in a section's spec directory.
 *
 * Filters out:
 * - AUDIT_ reports
 * - veo.json (Veo override prompts)
 * - Files with [veo:] on the first line (Veo generation prompts)
 * - The main spec.md UNLESS it's the only Remotion spec (fallback component)
 */
function listSpecComponents(specDir: string): string[] {
  const absDir = path.isAbsolute(specDir) ? specDir : path.join(process.cwd(), specDir);
  if (!fs.existsSync(absDir)) return [];

  const names: Set<string> = new Set();
  let hasMainSpec = false;

  const walk = (dir: string) => {
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(p);
      if (entry.isFile()) {
        // Skip audit reports and non-component metadata files
        if (entry.name.startsWith("AUDIT_")) continue;
        if (entry.name === "veo.json") continue;
        const base = path.basename(entry.name, path.extname(entry.name));
        // Track main spec.md but don't add it yet
        if (base === "spec") { hasMainSpec = true; continue; }
        if (base === "veo") continue;
        // Skip Veo generation prompts (first line contains [veo:])
        if (entry.name.endsWith(".md") && isVeoPromptSpec(p)) continue;
        names.add(base);
      }
    }
  };

  walk(absDir);

  // If no individual component specs were found but a main spec.md exists,
  // use a fallback component name so Claude generates at least one visual
  // Remotion component for this section.
  if (names.size === 0 && hasMainSpec) {
    const sectionId = path.basename(absDir);
    names.add(`${sectionId}_main`);
  }

  return Array.from(names);
}

function buildComponent(name: string): CompositionComponent {
  const filePath = path.join(REMOTION_DIR, `${name}.tsx`);
  const exists = fs.existsSync(filePath);
  return {
    name,
    status: exists ? "done" : "missing",
    error: null,
  };
}

export async function GET(): Promise<NextResponse> {
  try {
    const config = loadProject();

    const sections: CompositionSection[] = config.sections.map((section) => {
      const componentNames = listSpecComponents(
        path.join("specs", section.specDir)
      );

      const wrapperNames = Array.from(
        new Set([`${section.id}Wrapper`, `${section.compositionId}Wrapper`])
      );

      return {
        id: section.id,
        label: section.label,
        components: componentNames.map(buildComponent),
        wrappers: wrapperNames.map(buildComponent),
      };
    });

    return NextResponse.json({ sections });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message, sections: [] },
      { status: 500 }
    );
  }
}
