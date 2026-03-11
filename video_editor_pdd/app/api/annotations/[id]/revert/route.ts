import { NextResponse } from "next/server";
import fs from "fs/promises";
import path from "path";
import { execSync } from "child_process";
import { getDb } from "@/lib/db";
import { revertFix } from "@/lib/git";
import { runPipelineStage } from "@/lib/jobs";
import { loadProject, getSection } from "@/lib/project";
import { renderSection, stitchFullVideo } from "@/lib/render";
import { getProjectDir } from "@/lib/projects";

export const dynamic = "force-dynamic";

type RouteParams = { params: Promise<{ id: string }> };

const VEO_MEDIA_EXTENSIONS = new Set([".mp4", ".webm", ".mov", ".m4v"]);

async function syncVeoOutputsToRemotionPublic() {
  const sourceDir = path.join(getProjectDir(), "outputs", "veo");
  const destDir = path.join(getProjectDir(), "remotion", "public", "veo");

  try {
    const entries = await fs.readdir(sourceDir, { withFileTypes: true });
    await fs.mkdir(destDir, { recursive: true });

    for (const entry of entries) {
      if (!entry.isFile()) {
        continue;
      }

      const ext = path.extname(entry.name).toLowerCase();
      if (!VEO_MEDIA_EXTENSIONS.has(ext)) {
        continue;
      }

      await fs.copyFile(
        path.join(sourceDir, entry.name),
        path.join(destDir, entry.name)
      );
    }
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== "ENOENT") {
      throw error;
    }
  }
}

export async function POST(_request: Request, { params }: RouteParams) {
  const { id: annotationId } = await params;
  const db = getDb();

  try {
    const row = db
      .prepare("SELECT fixCommitSha, sectionId, analysis FROM annotations WHERE id = ?")
      .get(annotationId) as
      | { fixCommitSha: string | null; sectionId: string; analysis: string | null }
      | undefined;

    if (!row) {
      return NextResponse.json({ error: "Annotation not found" }, { status: 404 });
    }

    if (!row.fixCommitSha) {
      return NextResponse.json({ error: "No fix commit to revert" }, { status: 404 });
    }

    const revertSha = revertFix(row.fixCommitSha);
    const analysis = row.analysis ? JSON.parse(row.analysis) : null;
    const fixType = analysis?.fixType ?? null;
    const project = loadProject();

    if (fixType === "veo") {
      await runPipelineStage("veo", { clips: [row.sectionId] }, () => {});
      await syncVeoOutputsToRemotionPublic();
    }

    const remotionDir = path.join(getProjectDir(), "remotion");
    const buildDir = path.join(remotionDir, "build");
    const webpackCacheDir = path.join(
      remotionDir,
      "node_modules",
      ".cache",
      "webpack"
    );
    await fs.rm(buildDir, { recursive: true, force: true });
    await fs.rm(webpackCacheDir, { recursive: true, force: true });
    execSync("npx remotion bundle src/index.ts --out build", {
      cwd: remotionDir,
      stdio: "pipe",
      timeout: 120_000,
    });

    const section = getSection(row.sectionId, project);
    const compositionId = section?.compositionId ?? row.sectionId;
    const outputPath = path.join("outputs", "sections", `${row.sectionId}.mp4`);
    await renderSection(compositionId, outputPath, () => {});

    const stitchedSectionPaths: string[] = [];
    for (const projectSection of project.sections ?? []) {
      const sectionVideoPath = path.join("outputs", "sections", `${projectSection.id}.mp4`);
      try {
        await fs.access(sectionVideoPath);
        stitchedSectionPaths.push(sectionVideoPath);
      } catch {
        // Skip missing section outputs.
      }
    }

    if (stitchedSectionPaths.length > 0) {
      await stitchFullVideo(
        stitchedSectionPaths,
        path.join("outputs", "full_video.mp4"),
        () => {}
      );
    }

    // Clear the fixCommitSha and mark as unresolved
    db.prepare(
      "UPDATE annotations SET fixCommitSha = NULL, resolved = 0 WHERE id = ?"
    ).run(annotationId);

    return NextResponse.json({
      revertCommitSha: revertSha,
      annotationId,
      sectionId: row.sectionId,
    });
  } catch (error) {
    console.error("Failed to revert fix:", error);
    return NextResponse.json({ error: "Failed to revert fix" }, { status: 500 });
  }
}
