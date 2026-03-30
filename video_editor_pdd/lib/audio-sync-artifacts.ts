import fs from "fs";
import path from "path";

export type AudioSyncArtifactSource = "accepted" | "failed";

export type AudioSyncArtifactPaths = {
  wordTimestampsPath: string;
  validationPath: string;
  source: AudioSyncArtifactSource;
};

function statMtimeMs(filePath: string): number | null {
  try {
    return fs.statSync(filePath).mtimeMs;
  } catch {
    return null;
  }
}

export function resolveLatestAudioSyncArtifactPaths(
  projectDir: string,
  sectionId: string,
): AudioSyncArtifactPaths {
  const sectionDir = path.join(projectDir, "outputs", "tts", sectionId);
  const acceptedWordPath = path.join(sectionDir, "word_timestamps.json");
  const acceptedValidationPath = path.join(sectionDir, "segment_validation.json");
  const failedWordPath = path.join(sectionDir, "word_timestamps.failed.json");
  const failedValidationPath = path.join(sectionDir, "segment_validation.failed.json");

  const acceptedWordMtimeMs = statMtimeMs(acceptedWordPath);
  const failedWordMtimeMs = statMtimeMs(failedWordPath);
  const useFailed =
    failedWordMtimeMs !== null &&
    (acceptedWordMtimeMs === null || failedWordMtimeMs > acceptedWordMtimeMs);

  return {
    wordTimestampsPath: useFailed ? failedWordPath : acceptedWordPath,
    validationPath: useFailed ? failedValidationPath : acceptedValidationPath,
    source: useFailed ? "failed" : "accepted",
  };
}

export type AudioSyncWordTimestamp = {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
};

export function loadLatestWordTimestamps(
  projectDir: string,
  sectionId: string,
): AudioSyncWordTimestamp[] {
  const { wordTimestampsPath } = resolveLatestAudioSyncArtifactPaths(projectDir, sectionId);
  if (!fs.existsSync(wordTimestampsPath)) {
    return [];
  }

  try {
    const raw = fs.readFileSync(wordTimestampsPath, "utf-8");
    const parsed = JSON.parse(raw);
    const words = Array.isArray(parsed)
      ? parsed
      : Array.isArray(parsed?.words)
        ? parsed.words
        : [];

    return words.filter((word: unknown): word is AudioSyncWordTimestamp => {
      return (
        typeof (word as AudioSyncWordTimestamp | undefined)?.word === "string" &&
        typeof (word as AudioSyncWordTimestamp | undefined)?.start === "number" &&
        typeof (word as AudioSyncWordTimestamp | undefined)?.end === "number"
      );
    });
  } catch {
    return [];
  }
}
