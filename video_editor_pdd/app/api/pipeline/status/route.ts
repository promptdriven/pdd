import fs from "fs";
import path from "path";
import { NextResponse } from "next/server";
import { isCompositionArtifactSetStale } from "@/app/api/pipeline/_lib/composition-manifest";
import { getDb } from "@/lib/db";
import { loadProject } from "@/lib/project";
import { getProjectDir } from "@/lib/projects";
import type { PipelineStage, StageStatus } from "@/lib/types";

export const dynamic = "force-dynamic";

type StageStatusEntry = {
  status: StageStatus;
  lastJobId: string | null;
  error: string | null;
  updatedAt: string | null;
  stale?: boolean;
};

// Canonical ordered list of all pipeline stages
const PIPELINE_STAGES: PipelineStage[] = [
  "setup",
  "script",
  "tts-script",
  "tts-render",
  "audio-sync",
  "specs",
  "veo",
  "compositions",
  "render",
  "audit",
];

type ManifestSegment = {
  id: string;
  sectionId: string;
};

function getOutputTtsDir(): string {
  return path.join(getProjectDir(), "outputs", "tts");
}

function readSegmentsManifest(): {
  manifestPath: string;
  manifestMtimeMs: number | null;
  segments: ManifestSegment[];
} {
  const manifestPath = path.join(getOutputTtsDir(), "segments.json");
  if (!fs.existsSync(manifestPath)) {
    return { manifestPath, manifestMtimeMs: null, segments: [] };
  }

  try {
    const raw = fs.readFileSync(manifestPath, "utf-8");
    const parsed = JSON.parse(raw) as {
      segments?: Array<{ id?: string; sectionId?: string }>;
    };
    const manifestMtimeMs = fs.statSync(manifestPath).mtimeMs;
    const segments = (parsed.segments ?? [])
      .map((segment) => {
        const id = typeof segment.id === "string" ? segment.id : "";
        const sectionId =
          typeof segment.sectionId === "string"
            ? segment.sectionId
            : id.replace(/_\d{3}$/, "");
        return { id, sectionId };
      })
      .filter(
        (segment): segment is ManifestSegment =>
          Boolean(segment.id) && Boolean(segment.sectionId)
      );
    return { manifestPath, manifestMtimeMs, segments };
  } catch {
    return { manifestPath, manifestMtimeMs: null, segments: [] };
  }
}

function safeStatMtimeMs(filePath: string): number | null {
  try {
    return fs.statSync(filePath).mtimeMs;
  } catch {
    return null;
  }
}

function isTtsRenderStageStale(): boolean {
  const { manifestMtimeMs, segments } = readSegmentsManifest();
  if (manifestMtimeMs == null || segments.length === 0) {
    return false;
  }

  const ttsDir = getOutputTtsDir();
  for (const segment of segments) {
    const wavPath = path.join(ttsDir, `${segment.id}.wav`);
    const wavMtimeMs = safeStatMtimeMs(wavPath);
    if (wavMtimeMs == null || wavMtimeMs < manifestMtimeMs) {
      return true;
    }
  }

  return false;
}

function getCurrentAudioSyncSections(): string[] {
  const { segments } = readSegmentsManifest();
  if (segments.length > 0) {
    return [...new Set(segments.map((segment) => segment.sectionId))];
  }

  try {
    return loadProject()
      .sections.map((section) => section.id)
      .filter((sectionId): sectionId is string => typeof sectionId === "string");
  } catch {
    return [];
  }
}

function latestSectionAudioMtimeMs(sectionId: string): number | null {
  const ttsDir = getOutputTtsDir();
  try {
    const entries = fs.readdirSync(ttsDir);
    let latest: number | null = null;
    for (const entry of entries) {
      if (!entry.startsWith(`${sectionId}_`) || !entry.endsWith(".wav")) {
        continue;
      }

      const mtimeMs = safeStatMtimeMs(path.join(ttsDir, entry));
      if (mtimeMs == null) {
        continue;
      }

      latest = latest == null ? mtimeMs : Math.max(latest, mtimeMs);
    }
    return latest;
  } catch {
    return null;
  }
}

function latestSectionSyncMtimeMs(sectionId: string): number | null {
  const sectionDir = path.join(getOutputTtsDir(), sectionId);
  const candidateFiles = [
    "word_timestamps.json",
    "word_timestamps.failed.json",
    "segment_validation.json",
    "segment_validation.failed.json",
  ];

  let latest: number | null = null;
  for (const fileName of candidateFiles) {
    const mtimeMs = safeStatMtimeMs(path.join(sectionDir, fileName));
    if (mtimeMs == null) {
      continue;
    }
    latest = latest == null ? mtimeMs : Math.max(latest, mtimeMs);
  }
  return latest;
}

function isAudioSyncStageStale(): boolean {
  if (isTtsRenderStageStale()) {
    return true;
  }

  for (const sectionId of getCurrentAudioSyncSections()) {
    const latestAudioMtime = latestSectionAudioMtimeMs(sectionId);
    if (latestAudioMtime == null) {
      return true;
    }

    const latestSyncMtime = latestSectionSyncMtimeMs(sectionId);
    if (latestSyncMtime == null || latestAudioMtime > latestSyncMtime) {
      return true;
    }
  }

  return false;
}

/**
 * GET /api/pipeline/status
 * Returns the current status of all pipeline stages.
 */
export async function GET(): Promise<NextResponse> {
  try {
    const db = getDb();
    const rows = db.prepare("SELECT * FROM pipeline_status").all() as Array<{
      stage: PipelineStage;
      status: StageStatus;
      lastJobId: string | null;
      error: string | null;
      updatedAt: string | null;
    }>;

    const stagesMap = {} as Record<PipelineStage, StageStatusEntry>;

    // Build map from existing rows
    for (const row of rows) {
      stagesMap[row.stage] = {
        status: row.status,
        lastJobId: row.lastJobId ?? null,
        error: row.error ?? null,
        updatedAt: row.updatedAt ?? null,
      };
    }

    // Fill missing stages with defaults
    for (const stage of PIPELINE_STAGES) {
      if (!stagesMap[stage]) {
        stagesMap[stage] = {
          status: "not_started",
          lastJobId: null,
          error: null,
          updatedAt: null,
        };
      }
    }

    if (isCompositionArtifactSetStale()) {
      stagesMap.compositions = {
        ...stagesMap.compositions,
        stale: true,
      };
    }

    if (isTtsRenderStageStale()) {
      stagesMap["tts-render"] = {
        ...stagesMap["tts-render"],
        stale: true,
      };
    }

    if (isAudioSyncStageStale()) {
      stagesMap["audio-sync"] = {
        ...stagesMap["audio-sync"],
        stale: true,
      };
    }

    return NextResponse.json({ stages: stagesMap });
  } catch (error) {
    console.error("Error fetching pipeline status:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
