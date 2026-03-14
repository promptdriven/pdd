import { NextResponse } from "next/server";
import { isCompositionArtifactSetStale } from "@/app/api/pipeline/_lib/composition-manifest";
import { getDb } from "@/lib/db";
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

    return NextResponse.json({ stages: stagesMap });
  } catch (error) {
    console.error("Error fetching pipeline status:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
