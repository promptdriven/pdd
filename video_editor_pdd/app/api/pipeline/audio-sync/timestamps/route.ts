import { NextRequest, NextResponse } from "next/server";
import fs from "fs/promises";
import path from "path";

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
    process.cwd(),
    "outputs",
    "tts",
    sectionId,
    "word_timestamps.json"
  );

  try {
    const raw = await fs.readFile(filePath, "utf-8");
    const parsed = JSON.parse(raw) as { words: WordTimestamp[] };

    return NextResponse.json({ words: parsed.words }, { status: 200 });
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
