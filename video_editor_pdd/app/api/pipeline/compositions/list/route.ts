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

function listSpecComponents(specDir: string): string[] {
  const absDir = path.isAbsolute(specDir) ? specDir : path.join(process.cwd(), specDir);
  if (!fs.existsSync(absDir)) return [];

  const names: Set<string> = new Set();

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
        const base = path.basename(entry.name, path.extname(entry.name));
        names.add(base);
      }
    }
  };

  walk(absDir);
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
