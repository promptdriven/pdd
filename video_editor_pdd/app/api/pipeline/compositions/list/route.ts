import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

import {
  getCompositionArtifactState,
  resolveSectionCompositionIds,
} from "@/app/api/pipeline/_lib/composition-manifest";
import { loadProject } from "@/lib/project";
import { getAppRemotionSrcDir, getProjectDir } from "@/lib/projects";
import type { Section } from "@/lib/types";

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

interface CompositionArtifactStatePayload {
  stale: boolean;
  message: string | null;
}

const getRemotionDir = () => getAppRemotionSrcDir();

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
function listSpecComponents(specDir: string, sectionId?: string): string[] {
  const absDir = path.isAbsolute(specDir) ? specDir : path.join(getProjectDir(), specDir);
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
    const fallbackId = sectionId ?? path.basename(absDir);
    names.add(`${fallbackId}_main`);
  }

  return Array.from(names);
}

function toPascalCase(s: string): string {
  return s.replace(/(^|_)(\w)/g, (_, __, c) => c.toUpperCase());
}

function componentArtifactExists(name: string, sectionId?: string): boolean {
  // Check component directory ({NN}-{PascalName}/index.ts) first
  const nnMatch = name.match(/^(\d{2})_/);
  const strippedPascal = nnMatch ? toPascalCase(name.slice(nnMatch[0].length)) : toPascalCase(name);
  const dirName = nnMatch ? `${nnMatch[1]}-${strippedPascal}` : strippedPascal;
  const remotionDir = getRemotionDir();
  const dirExists = fs.existsSync(path.join(remotionDir, dirName, "index.ts"));
  // Also check section-prefixed PascalCase directory (e.g., Part1Economics06StatCalloutUplevel/)
  let pascalDirExists = false;
  if (!dirExists && sectionId && nnMatch) {
    const sectionPascal = toPascalCase(sectionId);
    const fullPascal = `${sectionPascal}${nnMatch[1]}${strippedPascal}`;
    pascalDirExists = fs.existsSync(path.join(remotionDir, fullPascal, "index.ts"));
  }
  // Then check section-scoped file ({sectionId}_{name}.tsx), fall back to flat ({name}.tsx)
  const scopedExists = sectionId && fs.existsSync(path.join(remotionDir, `${sectionId}_${name}.tsx`));
  const flatExists = fs.existsSync(path.join(remotionDir, `${name}.tsx`));
  return dirExists || pascalDirExists || scopedExists || flatExists;
}

function isComponentRegistered(name: string, section: Pick<Section, "id" | "compositions">): boolean {
  const registeredIds = resolveSectionCompositionIds(section);
  if (registeredIds.length === 0) {
    return true;
  }

  return (
    registeredIds.includes(name) ||
    registeredIds.includes(`${section.id}_${name}`)
  );
}

function buildComponent(name: string, section: Pick<Section, "id" | "compositions">): CompositionComponent {
  const artifactExists = componentArtifactExists(name, section.id);
  const registered = isComponentRegistered(name, section);

  if (artifactExists && !registered) {
    return {
      name,
      status: "missing",
      error: "Generated artifact exists on disk but is not registered in the current section composition graph. Regenerate this component in Stage 8.",
    };
  }

  return {
    name,
    status: artifactExists ? "done" : "missing",
    error: null,
  };
}

function buildWrapper(name: string, section: { id: string; compositionId: string }): CompositionComponent {
  // Wrappers can exist as:
  // 1. {sectionId}/index.tsx  (Python-generated section wrapper)
  // 2. {compositionId}.tsx    (Claude-generated section composition)
  // 3. {name}.tsx             (flat file matching wrapper name directly)
  const remotionDir = getRemotionDir();
  const indexExists = fs.existsSync(path.join(remotionDir, section.id, "index.tsx"));
  const compositionExists = fs.existsSync(path.join(remotionDir, `${section.compositionId}.tsx`));
  const flatExists = fs.existsSync(path.join(remotionDir, `${name}.tsx`));
  return {
    name,
    status: indexExists || compositionExists || flatExists ? "done" : "missing",
    error: null,
  };
}

export async function GET(): Promise<NextResponse> {
  try {
    const config = loadProject();

    const sections: CompositionSection[] = config.sections.map((section) => {
      const componentNames = listSpecComponents(
        path.join("specs", section.specDir),
        section.id
      );

      const wrapperNames = Array.from(
        new Set([`${section.id}Wrapper`, `${section.compositionId}Wrapper`])
      );

      return {
        id: section.id,
        label: section.label,
        components: componentNames.map((n) => buildComponent(n, section)),
        wrappers: wrapperNames.map((n) => buildWrapper(n, section)),
      };
    });

    const artifactState = getCompositionArtifactState();
    return NextResponse.json({
      sections,
      artifactState: {
        stale: artifactState.stale,
        message: artifactState.stale
          ? "Generated composition outputs are stale relative to the current generator/runtime. Regenerate compositions before previewing or rendering."
          : null,
      } satisfies CompositionArtifactStatePayload,
    });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message, sections: [] },
      { status: 500 }
    );
  }
}
