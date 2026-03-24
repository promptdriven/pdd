import fs from "fs";
import path from "path";

import { getProjectDir } from "@/lib/projects";

export type NarrationSegment = {
  id: string;
  sectionId: string;
  startSeconds?: number;
  endSeconds?: number;
  text: string;
  cleanText: string;
};

type NarrationManifest = {
  segments: NarrationSegment[];
};

type WordTimestamp = {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
};

/**
 * Load the enriched segments.json narration manifest from `outputs/tts/segments.json`.
 * Returns null when the manifest does not exist or cannot be parsed.
 */
export function loadNarrationManifest(
  projectDir = getProjectDir()
): NarrationManifest | null {
  const manifestPath = path.join(projectDir, "outputs", "tts", "segments.json");
  if (!fs.existsSync(manifestPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
    if (!parsed || !Array.isArray(parsed.segments)) {
      return null;
    }
    return parsed as NarrationManifest;
  } catch {
    return null;
  }
}

/**
 * Return narration segments for a specific section, enriched with timing.
 *
 * When segments already have `startSeconds`/`endSeconds` (from the enriched
 * manifest), those values are used directly. Otherwise falls back to loading
 * `word_timestamps.json` for the section and deriving timing from word boundaries.
 */
export function resolveSegmentTimingForSection(
  sectionId: string,
  projectDir = getProjectDir()
): NarrationSegment[] {
  const manifest = loadNarrationManifest(projectDir);
  if (!manifest) {
    return [];
  }

  const sectionSegments = manifest.segments.filter(
    (seg) => seg.sectionId === sectionId
  );

  // If all segments already have timing, return as-is
  const allTimed = sectionSegments.every(
    (seg) =>
      typeof seg.startSeconds === "number" &&
      typeof seg.endSeconds === "number"
  );
  if (allTimed) {
    return sectionSegments;
  }

  // Fall back: load word_timestamps.json and derive boundaries
  const words = loadWordTimestamps(projectDir, sectionId);
  if (!words || words.length === 0) {
    return sectionSegments;
  }

  return sectionSegments.map((seg) => {
    if (
      typeof seg.startSeconds === "number" &&
      typeof seg.endSeconds === "number"
    ) {
      return seg;
    }

    const matching = words.filter((w) => w.segmentId === seg.id);
    if (matching.length === 0) {
      return seg;
    }

    return {
      ...seg,
      startSeconds: Math.min(...matching.map((w) => w.start)),
      endSeconds: Math.max(...matching.map((w) => w.end)),
    };
  });
}

function loadWordTimestamps(
  projectDir: string,
  sectionId: string
): WordTimestamp[] | null {
  const tsPath = path.join(
    projectDir,
    "outputs",
    "tts",
    sectionId,
    "word_timestamps.json"
  );
  if (!fs.existsSync(tsPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(fs.readFileSync(tsPath, "utf-8"));
    const words: WordTimestamp[] = Array.isArray(parsed)
      ? parsed
      : parsed.words ?? [];
    return words;
  } catch {
    return null;
  }
}
