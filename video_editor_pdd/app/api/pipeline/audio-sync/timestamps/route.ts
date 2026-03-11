import { NextRequest, NextResponse } from "next/server";
import fs from "fs/promises";
import path from "path";
import { getProjectDir } from "@/lib/projects";

interface WordTimestamp {
  word: string;
  start: number;
  end: number;
  segmentId: string;
}

/**
 * GET /api/pipeline/audio-sync/timestamps?section=X
 * Returns word timestamps JSON for a given section.
 */
export async function GET(request: NextRequest): Promise<NextResponse> {
  const { searchParams } = new URL(request.url);
  const sectionId = searchParams.get("section");

  if (!sectionId) {
    return NextResponse.json(
      { error: "Missing required query param: section" },
      { status: 400 }
    );
  }

  const filePath = path.join(
    getProjectDir(),
    "outputs",
    "tts",
    sectionId,
    "word_timestamps.json"
  );

  try {
    const raw = await fs.readFile(filePath, "utf-8");
    const parsed = JSON.parse(raw);

    // Normalize: file may be a raw array or { words: [...] }
    const words: WordTimestamp[] = Array.isArray(parsed)
      ? parsed
      : Array.isArray(parsed?.words)
      ? parsed.words
      : [];

    return NextResponse.json({ words }, { status: 200 });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") {
      return NextResponse.json(
        { error: "Timestamps not found" },
        { status: 404 }
      );
    }

    console.error("Failed to read timestamps:", err);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
