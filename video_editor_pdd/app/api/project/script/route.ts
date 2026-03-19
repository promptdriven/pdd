import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";
import { getProjectDir } from "@/lib/projects";
import { normalizeSectionKey, parseScriptSections } from "@/lib/spec-script-context";

export const dynamic = "force-dynamic";

/** Map the `?file=` query parameter to a filename under `narrative/`. */
function resolveScriptPath(request: Request): string {
  const url = new URL(request.url);
  const file = url.searchParams.get("file") ?? "main";
  const filename = file === "tts" ? "tts_script.md" : "main_script.md";
  return path.join(getProjectDir(), "narrative", filename);
}

function tokenOverlapScore(left: string, right: string): number {
  const leftTokens = left.split(" ").filter(Boolean);
  const rightTokens = right.split(" ").filter(Boolean);
  if (leftTokens.length === 0 || rightTokens.length === 0) {
    return 0;
  }

  const rightSet = new Set(rightTokens);
  const overlap = leftTokens.filter((token) => rightSet.has(token)).length;
  return overlap / Math.max(leftTokens.length, rightTokens.length);
}

function extractSectionScriptContent(
  content: string,
  sectionId: string
): { sectionHeading: string | null; sectionContent: string | null } {
  const scriptSections = parseScriptSections(content);
  if (scriptSections.length === 0) {
    return { sectionHeading: null, sectionContent: null };
  }

  const normalizedTarget = normalizeSectionKey(sectionId);
  let bestIndex = -1;
  let bestScore = 0;

  scriptSections.forEach((scriptSection, index) => {
    const normalizedHeading = normalizeSectionKey(scriptSection.heading);
    const condensedHeading = normalizedHeading.replace(/\s+/g, "");
    const condensedTarget = normalizedTarget.replace(/\s+/g, "");

    let score = 0;
    if (normalizedHeading === normalizedTarget) {
      score = 100;
    } else if (condensedHeading === condensedTarget) {
      score = 95;
    } else if (
      normalizedHeading.includes(normalizedTarget) ||
      normalizedTarget.includes(normalizedHeading)
    ) {
      score = 80;
    } else {
      score = Math.round(tokenOverlapScore(normalizedHeading, normalizedTarget) * 100);
    }

    if (score > bestScore) {
      bestScore = score;
      bestIndex = index;
    }
  });

  if (bestIndex < 0 || bestScore < 35) {
    return { sectionHeading: null, sectionContent: null };
  }

  const lines = content.split(/\r?\n/);
  const current = scriptSections[bestIndex];
  const next = scriptSections[bestIndex + 1];
  const startLine = Math.max(0, current.startLine - 1);
  const endLine = next ? Math.max(startLine, next.startLine - 1) : lines.length;
  const sectionContent = lines.slice(startLine, endLine).join("\n").trim();

  return {
    sectionHeading: current.heading,
    sectionContent: sectionContent || null,
  };
}

/**
 * GET /api/project/script?file=main|tts
 * Reads the requested script file and returns its content as JSON { content }.
 * Defaults to main_script.md when `file` is omitted.
 * Returns 404 if the file does not exist.
 */
export async function GET(request: Request): Promise<NextResponse> {
  try {
    const url = new URL(request.url);
    const sectionId = url.searchParams.get("section");
    const filePath = resolveScriptPath(request);

    if (!fs.existsSync(filePath)) {
      return NextResponse.json(
        { error: "Script file not found" },
        { status: 404 }
      );
    }

    const content = fs.readFileSync(filePath, "utf-8");
    const { sectionHeading, sectionContent } = sectionId
      ? extractSectionScriptContent(content, sectionId)
      : { sectionHeading: null, sectionContent: null };

    return NextResponse.json(
      { content, sectionHeading, sectionContent },
      { status: 200 }
    );
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
