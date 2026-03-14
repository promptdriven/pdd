import { NextRequest, NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { Readable } from "stream";

import { loadProject } from "@/lib/project";
import { renderStill } from "@/lib/render";
import { getAppRemotionSrcDir, getProjectDir } from "@/lib/projects";
import {
  getCompositionArtifactState,
  resolveSectionCompositionIds,
} from "@/app/api/pipeline/_lib/composition-manifest";

const FPS = 30;

type PreviewSection = {
  id: string;
  compositionId: string;
  specDir?: string;
  compositions?: Array<string | { id: string; [key: string]: unknown }>;
};

function toPascalCase(s: string): string {
  return s.replace(/(^|_)(\w)/g, (_, __, c) => c.toUpperCase());
}

function componentArtifactExists(
  sectionId: string,
  componentName: string
): { resolvedId: string; compositionId: string } | null {
  const remotionSrc = getAppRemotionSrcDir();
  const scopedName = `${sectionId}_${componentName}`;
  const candidates: Array<{ resolvedId: string; filePath: string }> = [
    {
      resolvedId: scopedName,
      filePath: path.join(remotionSrc, `${scopedName}.tsx`),
    },
    {
      resolvedId: componentName,
      filePath: path.join(remotionSrc, `${componentName}.tsx`),
    },
  ];

  const nnMatch = componentName.match(/^(\d{2})_/);
  if (nnMatch) {
    const strippedPascal = toPascalCase(componentName.slice(nnMatch[0].length));
    const dashedDirName = `${nnMatch[1]}-${strippedPascal}`;
    const sectionPascal = toPascalCase(sectionId);
    const prefixedDirName = `${sectionPascal}${nnMatch[1]}${strippedPascal}`;
    candidates.push(
      {
        resolvedId: componentName,
        filePath: path.join(remotionSrc, dashedDirName, "index.ts"),
      },
      {
        resolvedId: componentName,
        filePath: path.join(remotionSrc, prefixedDirName, "index.ts"),
      }
    );
  } else {
    const plainDirName = toPascalCase(componentName);
    candidates.push({
      resolvedId: componentName,
      filePath: path.join(remotionSrc, plainDirName, "index.ts"),
    });
  }

  for (const candidate of candidates) {
    if (!fs.existsSync(candidate.filePath)) {
      continue;
    }

    return {
      resolvedId: candidate.resolvedId,
      compositionId: compToRemotionId(candidate.resolvedId, sectionId),
    };
  }

  return null;
}

/**
 * Convert a composition name + section ID to the Remotion composition ID
 * that Root.tsx registers (PascalCase identifier → kebab-case).
 */
function compToRemotionId(compId: string, sectionId: string): string {
  let pascal = toPascalCase(compId);
  // If PascalCase starts with a digit, prefix with section PascalCase
  if (/^\d/.test(pascal)) {
    pascal = toPascalCase(sectionId) + pascal;
  }
  // PascalCase → kebab-case
  return pascal.replace(/([a-z0-9])([A-Z])/g, "$1-$2").toLowerCase();
}

/**
 * Resolve a component name to a Remotion compositionId by scanning project.json sections.
 *
 * Individual components are registered in Root.tsx under their section-scoped name
 * (e.g., "cold_open_title_card"), so we return that name directly. Wrappers and
 * fallback _main components resolve to the section's compositionId.
 *
 * When sectionId is provided, only that section is checked — this disambiguates
 * components like "title_card" that appear in multiple sections.
 */
function resolvePreviewTarget(
  componentName: string,
  sectionId?: string
): { compositionId: string; section: PreviewSection } | null {
  const config = loadProject();
  const sections = sectionId
    ? config.sections.filter(
        (s: { id: string }) => s.id === sectionId
      )
    : config.sections;

  for (const section of sections as PreviewSection[]) {
    const comps = resolveSectionCompositionIds(section);
    // Check if the section-scoped name is in compositions — return its
    // Remotion composition ID (PascalCase → kebab-case to match Root.tsx).
    const scopedName = `${section.id}_${componentName}`;
    if (comps.includes(scopedName)) {
      return {
        compositionId: compToRemotionId(scopedName, section.id),
        section,
      };
    }
    // Check if the component name is already section-scoped in the list
    if (comps.includes(componentName)) {
      return {
        compositionId: compToRemotionId(componentName, section.id),
        section,
      };
    }
    // Fallback _main components → section wrapper
    if (componentName === `${section.id}_main`) {
      return { compositionId: section.compositionId, section };
    }
    // Wrapper names → section wrapper
    if (
      componentName === `${section.compositionId}Wrapper` ||
      componentName === `${section.id}Wrapper`
    ) {
      return { compositionId: section.compositionId, section };
    }

    const artifactMatch = componentArtifactExists(section.id, componentName);
    if (artifactMatch) {
      return {
        compositionId: artifactMatch.compositionId,
        section,
      };
    }
  }
  return null;
}

function resolvePreviewSpec(
  componentName: string,
  section: PreviewSection
): { specPath: string | null; specContent: string | null } {
  if (!section.specDir) {
    return { specPath: null, specContent: null };
  }

  const specDir = path.join(getProjectDir(), "specs", section.specDir);
  const candidateNames = new Set<string>();
  candidateNames.add(`${componentName}.md`);

  if (componentName.startsWith(`${section.id}_`)) {
    candidateNames.add(`${componentName.slice(section.id.length + 1)}.md`);
  }

  if (
    componentName === `${section.id}_main` ||
    componentName === `${section.compositionId}Wrapper` ||
    componentName === `${section.id}Wrapper`
  ) {
    candidateNames.add("spec.md");
  }

  for (const fileName of candidateNames) {
    const candidatePath = path.join(specDir, fileName);
    if (!fs.existsSync(candidatePath)) {
      continue;
    }

    return {
      specPath: path.relative(getProjectDir(), candidatePath),
      specContent: fs.readFileSync(candidatePath, "utf-8"),
    };
  }

  return { specPath: null, specContent: null };
}

/**
 * Build a cache-safe filename for the preview PNG.
 * When a sectionId is provided, prefix it to avoid collisions
 * (e.g. "title_card" exists in multiple sections).
 */
function previewFilename(componentName: string, sectionId?: string): string {
  const previewsDir = path.join(getProjectDir(), "outputs", "previews");
  const base = sectionId ? `${sectionId}--${componentName}` : componentName;
  return path.join(previewsDir, `${base}.png`);
}

/**
 * GET /api/pipeline/compositions/preview?component=<name>[&section=<id>][&raw=1]
 *
 * Without raw: renders a still at frame 30 (1s), saves to outputs/previews/,
 * returns JSON { url } pointing to the raw image.
 *
 * With raw=1: serves the cached PNG directly as image/png.
 */
export async function GET(request: NextRequest): Promise<Response> {
  const { searchParams } = new URL(request.url);
  const componentName = searchParams.get("component");
  const sectionId = searchParams.get("section") ?? undefined;

  if (!componentName) {
    return NextResponse.json(
      { error: "Missing component query parameter" },
      { status: 400 }
    );
  }

  const artifactState = getCompositionArtifactState();
  if (artifactState.stale) {
    return NextResponse.json(
      {
        error:
          "Generated composition outputs are stale relative to the current generator/runtime. Rerun Stage 8 Generate All Compositions.",
        stale: true,
      },
      { status: 409 }
    );
  }

  const pngPath = previewFilename(componentName, sectionId);

  // Serve cached PNG directly
  if (searchParams.get("raw") === "1") {
    if (!fs.existsSync(pngPath)) {
      return NextResponse.json({ error: "Preview not found" }, { status: 404 });
    }
    const stat = fs.statSync(pngPath);
    const nodeStream = fs.createReadStream(pngPath);
    const webStream = Readable.toWeb(nodeStream) as ReadableStream;
    return new NextResponse(webStream, {
      status: 200,
      headers: {
        "Content-Type": "image/png",
        "Content-Length": String(stat.size),
        "Cache-Control": "public, max-age=60",
      },
    });
  }

  // Render a new still
  const previewTarget = resolvePreviewTarget(componentName, sectionId);
  if (!previewTarget) {
    return NextResponse.json(
      { error: `Cannot resolve compositionId for "${componentName}"` },
      { status: 404 }
    );
  }

  try {
    await renderStill(previewTarget.compositionId, FPS, pngPath);
    const qs = new URLSearchParams({ component: componentName, raw: "1" });
    if (sectionId) qs.set("section", sectionId);
    const url = `/api/pipeline/compositions/preview?${qs}`;
    const { specPath, specContent } = resolvePreviewSpec(
      componentName,
      previewTarget.section
    );
    return NextResponse.json({ url, specPath, specContent });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Render failed";
    return NextResponse.json({ error: message }, { status: 500 });
  }
}
