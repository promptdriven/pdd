import { NextRequest, NextResponse } from "next/server";
import {
  resolveProjectWorkspace,
  setSelectedProjectId,
} from "@/lib/projects";

export const dynamic = "force-dynamic";

export async function POST(request: NextRequest): Promise<NextResponse> {
  let body: { projectId?: string } | null = null;

  try {
    body = (await request.json()) as { projectId?: string };
  } catch {
    return NextResponse.json({ error: "Invalid JSON" }, { status: 400 });
  }

  const projectId = body?.projectId?.trim();
  if (!projectId) {
    return NextResponse.json({ error: "Missing projectId" }, { status: 400 });
  }

  const project = resolveProjectWorkspace(projectId);
  if (!project) {
    return NextResponse.json({ error: "Project not found" }, { status: 404 });
  }

  setSelectedProjectId(project.id);

  return NextResponse.json({
    ok: true,
    project: {
      id: project.id,
      name: project.name,
    },
  });
}
