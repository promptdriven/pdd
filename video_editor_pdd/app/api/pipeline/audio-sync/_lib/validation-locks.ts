import crypto from "crypto";
import fs from "fs/promises";
import path from "path";

export interface AudioSyncValidationLockEntry {
  segmentId: string;
  audioFingerprint: string;
  acceptedAt: string;
}

export interface AudioSyncValidationLockFile {
  segments: Record<string, AudioSyncValidationLockEntry>;
}

export function getAudioSyncValidationLocksPath(
  projectDir: string,
  sectionId: string
): string {
  return path.join(
    projectDir,
    "outputs",
    "tts",
    sectionId,
    "segment_validation_overrides.json"
  );
}

export async function loadAudioSyncValidationLocks(
  projectDir: string,
  sectionId: string
): Promise<AudioSyncValidationLockFile> {
  const lockPath = getAudioSyncValidationLocksPath(projectDir, sectionId);
  try {
    const raw = await fs.readFile(lockPath, "utf-8");
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed !== "object") {
      return { segments: {} };
    }
    return {
      segments:
        parsed.segments && typeof parsed.segments === "object"
          ? parsed.segments
          : {},
    };
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
      console.error("Failed to read audio-sync validation locks:", error);
    }
    return { segments: {} };
  }
}

export async function saveAudioSyncValidationLocks(
  projectDir: string,
  sectionId: string,
  locks: AudioSyncValidationLockFile
): Promise<void> {
  const lockPath = getAudioSyncValidationLocksPath(projectDir, sectionId);
  const segmentIds = Object.keys(locks.segments);
  if (segmentIds.length === 0) {
    try {
      await fs.unlink(lockPath);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
        throw error;
      }
    }
    return;
  }

  await fs.writeFile(lockPath, JSON.stringify(locks, null, 2), "utf-8");
}

export async function computeFileSha256(filePath: string): Promise<string> {
  const contents = await fs.readFile(filePath);
  return crypto.createHash("sha256").update(contents).digest("hex");
}

export async function computeSegmentAudioFingerprintMap(
  projectDir: string,
  segmentIds: string[]
): Promise<Record<string, string>> {
  const fingerprints: Record<string, string> = {};
  for (const segmentId of segmentIds) {
    const wavPath = path.join(projectDir, "outputs", "tts", `${segmentId}.wav`);
    try {
      fingerprints[segmentId] = await computeFileSha256(wavPath);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
        console.error("Failed to fingerprint segment audio:", error);
      }
    }
  }
  return fingerprints;
}

export function applyAudioSyncValidationLocks(
  validation: {
    segments: Array<Record<string, unknown>>;
    summary: {
      passCount: number;
      warnCount: number;
      failCount: number;
      skipCount: number;
    };
  },
  locks: AudioSyncValidationLockFile,
  audioFingerprints: Record<string, string>
) {
  if (!validation.segments.length || Object.keys(locks.segments).length === 0) {
    return validation;
  }

  const nextSegments = validation.segments.map((segment) => {
    const segmentId = typeof segment.segmentId === "string" ? segment.segmentId : null;
    if (!segmentId) {
      return segment;
    }

    const lock = locks.segments[segmentId];
    if (!lock) {
      return segment;
    }

    const rowFingerprint =
      typeof segment.audioFingerprint === "string"
        ? segment.audioFingerprint
        : audioFingerprints[segmentId];
    if (!rowFingerprint || rowFingerprint !== lock.audioFingerprint) {
      return segment;
    }

    return {
      ...segment,
      locked: true,
      manuallyAccepted: true,
      statusBeforeOverride:
        typeof segment.status === "string" ? segment.status : undefined,
      matchRatioBeforeOverride:
        typeof segment.matchRatio === "number" ? segment.matchRatio : null,
      status: "pass",
    };
  });

  const summary = {
    passCount: 0,
    warnCount: 0,
    failCount: 0,
    skipCount: 0,
  };

  for (const segment of nextSegments) {
    const status = typeof segment.status === "string" ? segment.status : "skip";
    const key = `${status}Count` as keyof typeof summary;
    summary[key] += 1;
  }

  return {
    segments: nextSegments,
    summary,
  };
}
