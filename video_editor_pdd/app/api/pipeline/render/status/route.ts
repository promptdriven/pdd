import { NextResponse } from "next/server";
import fs from "fs";
import path from "path";

import { loadProject } from "@/lib/project";
import { getProjectDir } from "@/lib/projects";
import { getSectionDuration } from "@/lib/render";

/**
 * GET /api/pipeline/render/status
 *
 * Returns render status for each section (missing / done) and info about
 * the stitched full video if it exists.
 */

interface SectionRenderStatus {
  id: string;
  durationSeconds: number;
  status: "missing" | "rendering" | "done" | "error";
  progress: number;
  updatedAtMs?: number;
}

interface FullVideoInfo {
  exists: boolean;
  sizeBytes?: number;
  durationSeconds?: number;
  stale?: boolean;
  updatedAtMs?: number;
}

export async function GET(): Promise<NextResponse> {
  try {
    const projectDir = getProjectDir();
    const sectionsDir = path.join(projectDir, "outputs", "sections");
    const fullVideoPath = path.join(projectDir, "outputs", "full_video.mp4");
    const config = loadProject();
    let newestSectionMtime = 0;

    const sections: SectionRenderStatus[] = config.sections.map((section) => {
      const outputPath = path.join(sectionsDir, `${section.id}.mp4`);
      const exists = fs.existsSync(outputPath);
      let updatedAtMs: number | undefined;
      if (exists) {
        try {
          const stat = fs.statSync(outputPath);
          updatedAtMs = stat.mtimeMs;
          newestSectionMtime = Math.max(
            newestSectionMtime,
            stat.mtimeMs
          );
        } catch {
          // Ignore stat errors for stale detection.
        }
      }

      return {
        id: section.id,
        durationSeconds: section.durationSeconds ?? 0,
        status: exists ? "done" : "missing",
        progress: exists ? 100 : 0,
        updatedAtMs,
      };
    });

    let fullVideo: FullVideoInfo = { exists: false };
    if (fs.existsSync(fullVideoPath)) {
      try {
        const stat = fs.statSync(fullVideoPath);
        let durationSeconds: number | undefined;
        try {
          durationSeconds = await getSectionDuration(fullVideoPath);
        } catch {
          // ffprobe unavailable — leave undefined
        }
        fullVideo = {
          exists: true,
          sizeBytes: stat.size,
          durationSeconds,
          stale: newestSectionMtime > stat.mtimeMs,
          updatedAtMs: stat.mtimeMs,
        };
      } catch {
        // Ignore stat errors
      }
    }

    return NextResponse.json({ sections, fullVideo });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    return NextResponse.json(
      { error: message, sections: [], fullVideo: { exists: false } },
      { status: 500 }
    );
  }
}
