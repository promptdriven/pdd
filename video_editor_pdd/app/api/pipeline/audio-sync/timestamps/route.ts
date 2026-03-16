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

interface SegmentValidationSummary {
  passCount: number;
  warnCount: number;
  failCount: number;
  skipCount: number;
}

const EMPTY_VALIDATION = {
  segments: [],
  summary: {
    passCount: 0,
    warnCount: 0,
    failCount: 0,
    skipCount: 0,
  } satisfies SegmentValidationSummary,
};

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
  const validationPath = path.join(
    getProjectDir(),
    "outputs",
    "tts",
    sectionId,
    "segment_validation.json"
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

    let validation = EMPTY_VALIDATION;
    try {
      const validationRaw = await fs.readFile(validationPath, "utf-8");
      const parsedValidation = JSON.parse(validationRaw);
      validation = {
        segments: Array.isArray(parsedValidation?.segments)
          ? parsedValidation.segments
          : [],
        summary:
          parsedValidation?.summary &&
          typeof parsedValidation.summary === "object"
            ? {
                passCount:
                  typeof parsedValidation.summary.passCount === "number"
                    ? parsedValidation.summary.passCount
                    : 0,
                warnCount:
                  typeof parsedValidation.summary.warnCount === "number"
                    ? parsedValidation.summary.warnCount
                    : 0,
                failCount:
                  typeof parsedValidation.summary.failCount === "number"
                    ? parsedValidation.summary.failCount
                    : 0,
                skipCount:
                  typeof parsedValidation.summary.skipCount === "number"
                    ? parsedValidation.summary.skipCount
                    : 0,
              }
            : EMPTY_VALIDATION.summary,
      };
    } catch (validationErr) {
      if ((validationErr as NodeJS.ErrnoException).code !== "ENOENT") {
        console.error("Failed to read segment validation:", validationErr);
      }
    }

    return NextResponse.json({ words, validation }, { status: 200 });
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
