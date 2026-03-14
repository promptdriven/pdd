// app/api/project/route.ts
import { NextResponse } from "next/server";
import { ZodError } from "zod";

import { loadProject, saveProject, validateProjectConfig } from "@/lib/project";
import type { ProjectConfig } from "@/lib/types";

export const dynamic = "force-dynamic";

/**
 * Helper for unsupported HTTP methods.
 */
function methodNotAllowed(): NextResponse {
  return NextResponse.json({ error: "Method not allowed" }, { status: 405 });
}

function shouldPreserveGeneratedSectionState(
  existingSection: ProjectConfig["sections"][number],
  incomingSection: ProjectConfig["sections"][number]
): boolean {
  return (
    existingSection.id === incomingSection.id &&
    existingSection.specDir === incomingSection.specDir &&
    existingSection.remotionDir === incomingSection.remotionDir &&
    existingSection.compositionId === incomingSection.compositionId
  );
}

function mergeSections(
  existingSections: ProjectConfig["sections"],
  incomingSections: ProjectConfig["sections"]
): ProjectConfig["sections"] {
  const existingById = new Map(existingSections.map((section) => [section.id, section]));

  return incomingSections.map((incomingSection) => {
    const existingSection = existingById.get(incomingSection.id);
    if (!existingSection) {
      return incomingSection;
    }

    if (!shouldPreserveGeneratedSectionState(existingSection, incomingSection)) {
      return incomingSection;
    }

    return {
      ...existingSection,
      ...incomingSection,
    };
  });
}

/**
 * GET /api/project
 * Loads project.json and returns the full ProjectConfig.
 */
export async function GET(_request: Request): Promise<NextResponse> {
  try {
    const config = loadProject();
    return NextResponse.json(config, { status: 200 });
  } catch (err) {
    if (err instanceof ZodError) {
      return NextResponse.json(
        { error: "Validation failed", issues: err.issues },
        { status: 400 }
      );
    }

    console.error("Error loading project:", err);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}

/**
 * PUT /api/project
 * Accepts Partial<ProjectConfig>, merges with existing config,
 * validates, saves, and returns updated ProjectConfig.
 */
export async function PUT(request: Request): Promise<NextResponse> {
  let body: Partial<ProjectConfig>;

  // Parse JSON body safely
  try {
    body = (await request.json()) as Partial<ProjectConfig>;
  } catch (err) {
    return NextResponse.json({ error: "Invalid JSON" }, { status: 400 });
  }

  try {
    const existing = loadProject();
    const merged = {
      ...existing,
      ...body,
      sections: body.sections
        ? mergeSections(
            existing.sections,
            body.sections as ProjectConfig["sections"]
          )
        : existing.sections,
    };
    const validated = validateProjectConfig(merged);

    saveProject(validated);

    return NextResponse.json(validated, { status: 200 });
  } catch (err) {
    if (err instanceof ZodError) {
      return NextResponse.json(
        { error: "Validation failed", issues: err.issues },
        { status: 400 }
      );
    }

    console.error("Error saving project:", err);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}

/**
 * Explicit 405 responses for unsupported methods.
 * (Next.js will also return 405 automatically if not defined,
 * but these provide a custom JSON error payload.)
 */
export async function POST(): Promise<NextResponse> {
  return methodNotAllowed();
}

export async function PATCH(): Promise<NextResponse> {
  return methodNotAllowed();
}

export async function DELETE(): Promise<NextResponse> {
  return methodNotAllowed();
}

export async function OPTIONS(): Promise<NextResponse> {
  return methodNotAllowed();
}

export async function HEAD(): Promise<NextResponse> {
  return methodNotAllowed();
}
