import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { getProjectDir } from "@/lib/projects";

export const dynamic = "force-dynamic";

/** Map the `?file=` query parameter to a filename under `narrative/`. */
function resolveScriptPath(request: Request): string {
  const url = new URL(request.url);
  const file = url.searchParams.get("file") ?? "main";
  const filename = file === "tts" ? "tts_script.md" : "main_script.md";
  return path.join(getProjectDir(), "narrative", filename);
}

/**
 * GET /api/project/script?file=main|tts
 * Reads the requested script file and returns its content as JSON { content }.
 * Defaults to main_script.md when `file` is omitted.
 * Returns 404 if the file does not exist.
 */
export async function GET(request: Request): Promise<NextResponse> {
  try {
    const filePath = resolveScriptPath(request);

    if (!fs.existsSync(filePath)) {
      return NextResponse.json(
        { error: "Script file not found" },
        { status: 404 }
      );
    }

    const content = fs.readFileSync(filePath, "utf-8");

    return NextResponse.json({ content }, { status: 200 });
  } catch (error) {
    console.error("Error reading script file:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}

/**
 * POST /api/project/script?file=tts
 * Accepts plain-text body and writes it atomically to the target script file.
 * Used by Stage3TtsScriptGen to auto-save the TTS script editor content.
 * Creates the narrative/ directory if it does not exist.
 */
export async function POST(request: Request): Promise<NextResponse> {
  try {
    const content = await request.text();
    const filePath = resolveScriptPath(request);

    // Ensure the narrative/ directory exists
    fs.mkdirSync(path.dirname(filePath), { recursive: true });

    // Atomic write: write to .tmp file then rename
    const tmpPath = filePath + ".tmp";
    fs.writeFileSync(tmpPath, content, "utf-8");
    fs.renameSync(tmpPath, filePath);

    return NextResponse.json({ ok: true }, { status: 200 });
  } catch (error) {
    console.error("Error writing script file:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}

/**
 * PUT /api/project/script
 * Accepts { content: string } and writes it atomically to narrative/main_script.md.
 * Creates the narrative/ directory if it does not exist.
 * Returns 400 if content is missing or not a string.
 */
export async function PUT(request: Request): Promise<NextResponse> {
  let body: unknown;

  try {
    body = await request.json();
  } catch {
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }

  try {
    const content =
      body && typeof body === "object" && "content" in body
        ? (body as { content?: unknown }).content
        : undefined;

    if (content === undefined || content === null || typeof content !== "string") {
      return NextResponse.json(
        { error: "Missing required field: content must be a string." },
        { status: 400 }
      );
    }

    const filePath = resolveScriptPath(request);

    // Ensure the narrative/ directory exists
    fs.mkdirSync(path.dirname(filePath), { recursive: true });

    // Atomic write: write to .tmp file then rename
    const tmpPath = filePath + ".tmp";
    fs.writeFileSync(tmpPath, content, "utf-8");
    fs.renameSync(tmpPath, filePath);

    return NextResponse.json({ ok: true }, { status: 200 });
  } catch (error) {
    console.error("Error writing script file:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
