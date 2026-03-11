import { NextRequest, NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { getProjectDir } from "@/lib/projects";

/**
 * GET /api/pipeline/specs/file?path=specs/00-cold-open/spec.md
 * Returns the file content as JSON { content: string }.
 *
 * PUT /api/pipeline/specs/file
 * Body: { path: string, content: string }
 * Writes (or overwrites) the spec file. Creates directories if needed.
 */

function resolveSafePath(relPath: string): string | null {
  const cwd = getProjectDir();
  const abs = path.resolve(cwd, relPath);

  // Ensure path stays within the project root
  if (!abs.startsWith(cwd)) return null;
  // Ensure it's under specs/
  if (!relPath.startsWith("specs/") && !relPath.startsWith("specs\\")) return null;

  return abs;
}

export async function GET(request: NextRequest): Promise<NextResponse> {
  const filePath = request.nextUrl.searchParams.get("path");

  if (!filePath) {
    return NextResponse.json(
      { error: "Missing 'path' query parameter" },
      { status: 400 }
    );
  }

  const abs = resolveSafePath(filePath);
  if (!abs) {
    return NextResponse.json(
      { error: "Invalid file path" },
      { status: 400 }
    );
  }

  if (!fs.existsSync(abs)) {
    return NextResponse.json({ content: "" });
  }

  const content = fs.readFileSync(abs, "utf-8");
  return NextResponse.json({ content });
}

export async function PUT(request: NextRequest): Promise<NextResponse> {
  const body = await request.json().catch(() => null);

  if (!body || typeof body.path !== "string" || typeof body.content !== "string") {
    return NextResponse.json(
      { error: "Body must include 'path' (string) and 'content' (string)" },
      { status: 400 }
    );
  }

  const abs = resolveSafePath(body.path);
  if (!abs) {
    return NextResponse.json(
      { error: "Invalid file path" },
      { status: 400 }
    );
  }

  fs.mkdirSync(path.dirname(abs), { recursive: true });
  fs.writeFileSync(abs, body.content, "utf-8");

  return NextResponse.json({ ok: true });
}
