import { NextResponse } from "next/server";
import {
  getCurrentProjectWorkspace,
  listProjectWorkspaces,
} from "@/lib/projects";

export const dynamic = "force-dynamic";

export async function GET(): Promise<NextResponse> {
  const projects = listProjectWorkspaces().map((project) => ({
    id: project.id,
    name: project.name,
  }));

  return NextResponse.json({
    projects,
    selectedProjectId: getCurrentProjectWorkspace().id,
  });
}
