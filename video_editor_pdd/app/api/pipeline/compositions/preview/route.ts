import { NextRequest, NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { Readable } from "stream";

import { loadProject } from "@/lib/project";
import { renderStill } from "@/lib/render";

const PREVIEWS_DIR = path.join(process.cwd(), "outputs", "previews");
const FPS = 30;

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
function resolveCompositionId(
  componentName: string,
  sectionId?: string
): string | null {
  const config = loadProject();
  const sections = sectionId
    ? config.sections.filter(
        (s: { id: string }) => s.id === sectionId
      )
    : config.sections;

  for (const section of sections) {
    const comps: string[] = section.compositions ?? [];
    // Check if the section-scoped name is in compositions — return its
    // hyphenated form as the Remotion composition ID (underscores are invalid).
    const scopedName = `${section.id}_${componentName}`;
    if (comps.includes(scopedName)) {
      return scopedName.replace(/_/g, "-");
    }
    // Check if the component name is already section-scoped in the list
    if (comps.includes(componentName)) {
      return componentName.replace(/_/g, "-");
    }
    // Fallback _main components → section wrapper
    if (componentName === `${section.id}_main`) {
      return section.compositionId;
    }
    // Wrapper names → section wrapper
    if (
      componentName === `${section.compositionId}Wrapper` ||
      componentName === `${section.id}Wrapper`
    ) {
      return section.compositionId;
    }
  }
  return null;
}

/**
 * Build a cache-safe filename for the preview PNG.
 * When a sectionId is provided, prefix it to avoid collisions
 * (e.g. "title_card" exists in multiple sections).
 */
function previewFilename(componentName: string, sectionId?: string): string {
  const base = sectionId ? `${sectionId}--${componentName}` : componentName;
  return path.join(PREVIEWS_DIR, `${base}.png`);
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
  const compositionId = resolveCompositionId(componentName, sectionId);
  if (!compositionId) {
    return NextResponse.json(
      { error: `Cannot resolve compositionId for "${componentName}"` },
      { status: 404 }
    );
  }

  try {
    await renderStill(compositionId, FPS, pngPath);
    const qs = new URLSearchParams({ component: componentName, raw: "1" });
    if (sectionId) qs.set("section", sectionId);
    const url = `/api/pipeline/compositions/preview?${qs}`;
    return NextResponse.json({ url });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Render failed";
    return NextResponse.json({ error: message }, { status: 500 });
  }
}
