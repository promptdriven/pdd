import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

export const dynamic = "force-dynamic";

/**
 * GET /api/project/script
 * Reads narrative/main_script.md and returns its content.
 * Returns 404 if the file does not exist.
 */
export async function GET(request: Request): Promise<NextResponse> {
  try {
    const filePath = path.join(process.cwd(), "narrative", "main_script.md");

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
 * PUT /api/project/script
 * Accepts { content: string } and writes it atomically to narrative/main_script.md.
 * Creates the narrative/ directory if it does not exist.
 * Returns 400 if content is missing or not a string.
 */
export async function PUT(request: Request): Promise<NextResponse> {
  try {
    const body = await request.json();
    const { content } = body;

    if (content === undefined || content === null || typeof content !== "string") {
      return NextResponse.json(
        { error: "Missing required field: content must be a string." },
        { status: 400 }
      );
    }

    const filePath = path.join(process.cwd(), "narrative", "main_script.md");

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