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

interface AudioSyncArtifactState {
  stale: boolean;
  message: string | null;
  source?: "accepted" | "failed";
  latestAudioUpdatedAtMs?: number;
  syncUpdatedAtMs?: number;
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

async function getAudioSyncArtifactState(
  sectionId: string,
  wordTimestampsPath: string,
  validationPath: string
): Promise<AudioSyncArtifactState> {
  const projectDir = getProjectDir();
  const ttsRoot = path.join(projectDir, "outputs", "tts");
  const prefix = `${sectionId}_`;

  let syncUpdatedAtMs: number | undefined;
  for (const syncPath of [wordTimestampsPath, validationPath]) {
    try {
      const stats = await fs.stat(syncPath);
      syncUpdatedAtMs =
        syncUpdatedAtMs === undefined
          ? stats.mtimeMs
          : Math.max(syncUpdatedAtMs, stats.mtimeMs);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
        console.error("Failed to stat audio-sync artifact:", error);
      }
    }
  }

  let latestAudioUpdatedAtMs: number | undefined;
  try {
    const entries = await fs.readdir(ttsRoot);
    for (const entry of entries) {
      if (!entry.startsWith(prefix) || !entry.endsWith(".wav")) {
        continue;
      }

      try {
        const stats = await fs.stat(path.join(ttsRoot, entry));
        latestAudioUpdatedAtMs =
          latestAudioUpdatedAtMs === undefined
            ? stats.mtimeMs
            : Math.max(latestAudioUpdatedAtMs, stats.mtimeMs);
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
          console.error("Failed to stat TTS audio artifact:", error);
        }
      }
    }
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
      console.error("Failed to inspect TTS output directory:", error);
    }
  }

  const stale =
    latestAudioUpdatedAtMs !== undefined &&
    syncUpdatedAtMs !== undefined &&
    latestAudioUpdatedAtMs > syncUpdatedAtMs;

  return {
    stale,
    message: stale
      ? "Audio sync data is stale relative to the current TTS audio. Re-run audio sync for this section."
      : null,
    latestAudioUpdatedAtMs,
    syncUpdatedAtMs,
  };
}

async function statMtimeMs(filePath: string): Promise<number | null> {
  try {
    const stats = await fs.stat(filePath);
    return stats.mtimeMs;
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
      console.error("Failed to stat audio-sync file:", error);
    }
    return null;
  }
}

async function resolveAudioSyncArtifactPaths(sectionId: string): Promise<{
  wordTimestampsPath: string;
  validationPath: string;
  source: "accepted" | "failed";
}> {
  const projectDir = getProjectDir();
  const sectionDir = path.join(projectDir, "outputs", "tts", sectionId);
  const acceptedWordPath = path.join(sectionDir, "word_timestamps.json");
  const acceptedValidationPath = path.join(sectionDir, "segment_validation.json");
  const failedWordPath = path.join(sectionDir, "word_timestamps.failed.json");
  const failedValidationPath = path.join(sectionDir, "segment_validation.failed.json");

  const acceptedWordMtimeMs = await statMtimeMs(acceptedWordPath);
  const failedWordMtimeMs = await statMtimeMs(failedWordPath);
  const useFailed =
    failedWordMtimeMs !== null &&
    (acceptedWordMtimeMs === null || failedWordMtimeMs > acceptedWordMtimeMs);

  return {
    wordTimestampsPath: useFailed ? failedWordPath : acceptedWordPath,
    validationPath: useFailed ? failedValidationPath : acceptedValidationPath,
    source: useFailed ? "failed" : "accepted",
  };
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

  try {
    const artifactPaths = await resolveAudioSyncArtifactPaths(sectionId);
    const raw = await fs.readFile(artifactPaths.wordTimestampsPath, "utf-8");
    const parsed = JSON.parse(raw);

    // Normalize: file may be a raw array or { words: [...] }
    const words: WordTimestamp[] = Array.isArray(parsed)
      ? parsed
      : Array.isArray(parsed?.words)
      ? parsed.words
      : [];

    let validation = EMPTY_VALIDATION;
    try {
      const validationRaw = await fs.readFile(artifactPaths.validationPath, "utf-8");
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

    const artifactState = await getAudioSyncArtifactState(
      sectionId,
      artifactPaths.wordTimestampsPath,
      artifactPaths.validationPath
    );
    artifactState.source = artifactPaths.source;

    return NextResponse.json({ words, validation, artifactState }, { status: 200 });
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
