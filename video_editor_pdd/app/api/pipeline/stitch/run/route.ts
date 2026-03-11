import { NextResponse } from "next/server";
import { randomUUID } from "crypto";
import path from "path";
import fs from "fs/promises";

import { stitchFullVideo } from "@/lib/render";
import { loadProject } from "@/lib/project";
import { getProjectDir } from "@/lib/projects";

/**
 * POST /api/pipeline/stitch/run
 *
 * Triggers stitching of all rendered section videos into a single full video.
 * Returns a jobId for tracking.
 */
export async function POST(): Promise<NextResponse> {
  try {
    const projectDir = getProjectDir();
    const project = loadProject();
    const sectionPaths = project.sections
      .map((s) => path.join(projectDir, "outputs", "sections", `${s.id}.mp4`))
      .filter((p) => {
        try {
          require("fs").accessSync(p);
          return true;
        } catch {
          return false;
        }
      });

    if (sectionPaths.length === 0) {
      return NextResponse.json(
        { error: "No rendered section videos found" },
        { status: 400 }
      );
    }

    const outputPath = path.join(projectDir, "outputs", "full_video.mp4");
    await fs.mkdir(path.join(projectDir, "outputs"), { recursive: true });

    const jobId = randomUUID();
    await stitchFullVideo(sectionPaths, outputPath, () => {});

    return NextResponse.json({ jobId }, { status: 200 });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Unknown error";
    console.error("Stitch run failed:", err);
    return NextResponse.json(
      { error: message },
      { status: 500 }
    );
  }
}
