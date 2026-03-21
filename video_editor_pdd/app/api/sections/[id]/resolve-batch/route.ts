// app/api/sections/[id]/resolve-batch/route.ts
import { NextResponse } from "next/server";
import fs from "fs/promises";
import path from "path";
import { execSync } from "child_process";
import { getDb } from "@/lib/db";
import { runClaudeFix } from "@/lib/claude";
import { createJob, runJob, runPipelineStage } from "@/lib/jobs";
import { renderSection, stitchFullVideo } from "@/lib/render";
import { loadProject, getSection } from "@/lib/project";
import { isGitAvailable, preFixCommitWithPaths, fixCommit } from "@/lib/git";
import type { Annotation } from "@/lib/types";
import { resolveAnnotationTarget } from "@/lib/annotation-target";
import { applyRemotionSpecFixForAnnotation } from "@/lib/remotion-spec-fix";
import { applyVeoPromptFixForAnnotation } from "@/lib/veo-prompt-fix";
import {
  getAppRemotionDir,
  getAppRemotionPublicDir,
  getAppScriptsDir,
  getProjectDir,
} from "@/lib/projects";
import {
  applyDeterministicRemotionFix,
  applyDeterministicVideoOverlay,
  extractRequestedHexColor,
  isDeterministicPipelineMode,
} from "@/lib/deterministic-pipeline";

export const dynamic = "force-dynamic";

/**
 * Concurrency control for batch resolve jobs.
 * Configurable via RESOLVE_CONCURRENCY env var (default: 1).
 * Prevents server overload from multiple concurrent resolve jobs
 * that each run Claude fixes + Remotion builds + section renders.
 */
const RESOLVE_CONCURRENCY = Math.max(
  1,
  parseInt(process.env.RESOLVE_CONCURRENCY ?? "1", 10) || 1
);
let activeResolveCount = 0;
const resolveQueue: Array<() => void> = [];

function acquireResolveSlot(): Promise<void> {
  if (activeResolveCount < RESOLVE_CONCURRENCY) {
    activeResolveCount++;
    return Promise.resolve();
  }
  return new Promise<void>((resolve) => {
    resolveQueue.push(resolve);
  });
}

function releaseResolveSlot(): void {
  const next = resolveQueue.shift();
  if (next) {
    next();
  } else {
    activeResolveCount = Math.max(0, activeResolveCount - 1);
  }
}

const VEO_MEDIA_EXTENSIONS = new Set([".mp4", ".webm", ".mov", ".m4v"]);

type RouteParams = { params: Promise<{ id: string }> };

function toPascalCase(value: string): string {
  return value
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0].toUpperCase() + part.slice(1))
    .join("");
}

function buildRemotionPrompt(annotation: Annotation): string {
  const analysisJson = annotation.analysis ? JSON.stringify(annotation.analysis, null, 2) : "none";
  return `
You are a Remotion developer fixing a visual issue in the "${annotation.sectionId}" section.

Issue details:
- Annotation ID: ${annotation.id}
- Timestamp: ${annotation.timestamp}s
- User note: ${annotation.text}
- Analysis: ${analysisJson}

Instructions:
1. Use Glob/Read tools to inspect the TSX source files in this directory (remotion/src/remotion/).
2. Identify which file(s) need to change to resolve the issue described above.
3. Apply the fix by editing the file(s) using the Edit or Write tool.
4. Return JSON confirming what you changed:
{
  "fixType": "remotion",
  "filesModified": ["list of relative file paths you edited"],
  "changeDescription": "concise description of the change made",
  "confidence": 0.0-1.0
}

Apply the fix NOW — do not just describe it. Edit the actual file(s).
`.trim();
}

async function syncVeoOutputsToRemotionPublic(onLog: (message: string) => void) {
  const sourceDir = path.join(getProjectDir(), "outputs", "veo");
  const destDir = path.join(getAppRemotionPublicDir(), "veo");

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
    if ((error as NodeJS.ErrnoException).code === "ENOENT") {
      return;
    }

    onLog(
      `Warning: failed to sync staged Veo assets: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

export async function POST(_request: Request, { params }: RouteParams) {
  const { id: sectionId } = await params;
  const db = getDb();

  try {
    // Check for optional annotationIds filter (from preview flow)
    let annotationIds: string[] | null = null;
    try {
      const body = await _request.json();
      if (body.annotationIds && Array.isArray(body.annotationIds)) {
        annotationIds = body.annotationIds;
      }
    } catch {
      // No body or invalid JSON — process all unresolved
    }

    // 1. Load unresolved annotations for the section
    let rows: Array<Record<string, unknown>>;
    if (annotationIds && annotationIds.length > 0) {
      const placeholders = annotationIds.map(() => '?').join(',');
      rows = db
        .prepare(
          `SELECT * FROM annotations WHERE id IN (${placeholders}) AND resolved = 0 ORDER BY timestamp ASC`
        )
        .all(...annotationIds) as Array<Record<string, unknown>>;
    } else {
      rows = db
        .prepare(
          `SELECT * FROM annotations WHERE sectionId = ? AND resolved = 0 ORDER BY timestamp ASC`
        )
        .all(sectionId) as Array<Record<string, unknown>>;
    }

    if (!rows || rows.length === 0) {
      return NextResponse.json(
        { jobId: null, message: "No unresolved annotations" },
        { status: 200 }
      );
    }

    // 2. Deserialize analysis_json → analysis
    const annotations: Annotation[] = rows.map((row) => {
      const analysisRaw = (row.analysis as string | null);
      const analysis = analysisRaw ? JSON.parse(analysisRaw) : null;

      return {
        id: String(row.id),
        sectionId: String(row.sectionId),
        timestamp: Number(row.timestamp),
        text: String(row.text ?? ""),
        videoFile: (row.videoFile as string | null) ?? null,
        drawingDataUrl: (row.drawingDataUrl as string | null) ?? null,
        compositeDataUrl: (row.compositeDataUrl as string | null) ?? null,
        analysis,
        resolved: Boolean(row.resolved),
        resolveJobId: (row.resolveJobId as string | null) ?? null,
        fixCommitSha: (row.fixCommitSha as string | null) ?? null,
        createdAt: String(row.createdAt ?? ""),
      };
    });

    // 3. Create top-level job
    const jobId = createJob("audit", { sectionId });

    // 4. Update resolve_job_id for all annotations
    const updateStmt = db.prepare(
      `UPDATE annotations SET resolveJobId = ? WHERE id = ?`
    );
    for (const ann of annotations) {
      updateStmt.run(jobId, ann.id);
    }

    // 5. Fire-and-forget execution (respects RESOLVE_CONCURRENCY limit)
    void runJob(jobId, async (onLog) => {
      await acquireResolveSlot();
      const projectDir = getProjectDir();
      const project = loadProject();
      const resolvedAnnotationIds = new Set<string>();
      const normalizedAnnotations = annotations.map((annotation) => {
        const target = resolveAnnotationTarget(project, {
          sectionId: annotation.sectionId,
          timestamp: annotation.timestamp,
          videoFile: annotation.videoFile,
        });

        if (target.normalized) {
          db.prepare("UPDATE annotations SET sectionId = ?, timestamp = ? WHERE id = ?").run(
            target.sectionId,
            target.timestamp,
            annotation.id
          );
        }

        return {
          ...annotation,
          sectionId: target.sectionId,
          timestamp: target.timestamp,
        };
      });

      const byFixType: Record<string, Annotation[]> = {
        remotion: [],
        veo: [],
        tts: [],
        manual: [],
        none: [],
      };

      for (const ann of normalizedAnnotations) {
        const fixType = ann.analysis?.fixType ?? "manual";
        if (byFixType[fixType]) byFixType[fixType].push(ann);
      }

      // Pre-fix git snapshot
      const gitAvail = isGitAvailable();
      if (gitAvail) {
        const preSha = preFixCommitWithPaths(sectionId, jobId, [
          path.join(getAppRemotionDir(), "src", "remotion"),
          path.join(projectDir, "specs"),
        ]);
        if (preSha) onLog(`Pre-fix snapshot committed: ${preSha.slice(0, 8)}`);
      }

      // Remotion fixes via Claude
      for (const ann of byFixType.remotion) {
        onLog(`Running Claude fix for annotation ${ann.id}`);
        const targetSection = project.sections.find(
          (section) => section.id === ann.sectionId
        );
        const stagedPaths = ["remotion/src/remotion/"];
        const remotionSourceDir = path.join(getAppRemotionDir(), "src", "remotion");
        if (targetSection) {
          const patch = applyRemotionSpecFixForAnnotation(
            projectDir,
            targetSection,
            ann
          );
          if (patch) {
            onLog(
              `Updated Remotion spec ${path.relative(projectDir, patch.specPath)}`
            );
            stagedPaths.push(patch.specPath);
          }
        }
        stagedPaths[0] = remotionSourceDir;
        if (isDeterministicPipelineMode()) {
          applyDeterministicRemotionFix(projectDir, ann.sectionId, ann.text, onLog);
        } else {
          await runClaudeFix(
            buildRemotionPrompt(ann),
            "remotion/src/remotion/",
            onLog
          );
        }

        // Git commit after fix
        if (gitAvail) {
          const sha = fixCommit(ann.id, ann.text.slice(0, 50), stagedPaths);
          if (sha) {
            onLog(`Fix committed: ${sha.slice(0, 8)}`);
            db.prepare("UPDATE annotations SET fixCommitSha = ? WHERE id = ?").run(sha, ann.id);
          }
        }

        resolvedAnnotationIds.add(ann.id);
      }

      // Veo fixes
      if (byFixType.veo.length > 0) {
        const veoClipTargets = new Set<string>();

        for (const ann of byFixType.veo) {
          const targetSection = project.sections.find(
            (section) => section.id === ann.sectionId
          );

          if (!targetSection) {
            veoClipTargets.add(ann.sectionId);
            continue;
          }

          const patch = applyVeoPromptFixForAnnotation(
            projectDir,
            targetSection,
            ann
          );

          if (patch) {
            onLog(
              `Updated Veo prompt for ${patch.clipId} in ${path.relative(projectDir, patch.specPath)}`
            );
            veoClipTargets.add(patch.clipId);

            if (gitAvail) {
              const sha = fixCommit(
                ann.id,
                ann.text.slice(0, 50),
                [patch.specPath]
              );
              if (sha) {
                onLog(`Fix committed: ${sha.slice(0, 8)}`);
                db.prepare("UPDATE annotations SET fixCommitSha = ? WHERE id = ?").run(sha, ann.id);
              }
            }

            resolvedAnnotationIds.add(ann.id);
          } else {
            onLog(
              `No Veo prompt rewrite derived for annotation ${ann.id}; regenerating ${ann.sectionId} with existing prompt sources`
            );
            veoClipTargets.add(ann.sectionId);
            onLog(
              `Leaving annotation ${ann.id} unresolved because no Veo prompt rewrite could be derived.`
            );
          }
        }

        const veoTargets = Array.from(veoClipTargets);
        onLog(`Running Veo regeneration for targets: ${veoTargets.join(", ")}`);
        await runPipelineStage("veo", { clips: veoTargets }, () => {});
      }

      // TTS fixes (placeholder)
      for (const ann of byFixType.tts) {
        onLog(`Queued TTS re-render for annotation ${ann.id} (pending)`);
      }

      // manual fixes are skipped
      for (const ann of byFixType.manual) {
        onLog(`Skipped manual annotation ${ann.id}`);
      }

      // Rebuild Remotion bundle so renders pick up the edited TSX
      const remotionDir = getAppRemotionDir();
      const buildDir = path.join(remotionDir, "build");
      const webpackCacheDir = path.join(
        remotionDir,
        "node_modules",
        ".cache",
        "webpack",
      );
      if (byFixType.veo.length > 0) {
        onLog("Syncing staged Veo assets...");
        await syncVeoOutputsToRemotionPublic(onLog);
      }
      onLog("Clearing stale bundle and webpack cache...");
      await fs.rm(buildDir, { recursive: true, force: true });
      await fs.rm(webpackCacheDir, { recursive: true, force: true });
      onLog("Regenerating Root.tsx...");
      execSync(
        `python3 "${path.join(getAppScriptsDir(), "generate_section_compositions.py")}" --project-dir "${getProjectDir()}" --remotion-dir "${getAppRemotionDir()}" --force`,
        {
        cwd: getProjectDir(),
        stdio: "pipe",
        timeout: 120_000,
        }
      );
      onLog("Rebuilding Remotion bundle...");
      execSync("npx remotion bundle src/index.ts --out build", {
        cwd: remotionDir,
        stdio: "pipe",
        timeout: 120_000,
      });
      onLog("Bundle rebuilt.");

      const affectedSections = Array.from(
        new Set(
          normalizedAnnotations
            .filter((annotation) => {
              const fixType = annotation.analysis?.fixType ?? "manual";
              return fixType !== "manual" && fixType !== "none";
            })
            .map((annotation) => annotation.sectionId)
        )
      );

      const sectionsToRender = affectedSections.length > 0 ? affectedSections : [sectionId];

      for (const targetSectionId of sectionsToRender) {
        const section = getSection(targetSectionId, project);
        const compositionId = section?.compositionId ?? `${toPascalCase(targetSectionId)}Section`;
        const outputPath = path.join(
          projectDir,
          "outputs",
          "sections",
          `${targetSectionId}.mp4`
        );
        onLog(`Rendering section ${targetSectionId} (${compositionId}) → ${outputPath}`);
        await renderSection(compositionId, outputPath, (progress) => {
          onLog.progress?.(progress.percent);
          onLog(progress.message);
        });
      }

      const stitchedSectionPaths: string[] = [];
      for (const projectSection of project.sections ?? []) {
        const sectionVideoPath = path.join(
          projectDir,
          "outputs",
          "sections",
          `${projectSection.id}.mp4`
        );
        try {
          await fs.access(sectionVideoPath);
          stitchedSectionPaths.push(sectionVideoPath);
        } catch {
          // Skip sections that do not have a rendered output yet.
        }
      }

      if (stitchedSectionPaths.length > 0) {
        const fullVideoOutputPath = path.join(projectDir, "outputs", "full_video.mp4");
        onLog(`Stitching full video → ${fullVideoOutputPath}`);
        await stitchFullVideo(stitchedSectionPaths, fullVideoOutputPath, (progress) => {
          onLog.progress?.(progress.percent);
          onLog(progress.message);
        });
      }

      if (isDeterministicPipelineMode() && byFixType.remotion.length > 0) {
        const firstRemotionSectionId = byFixType.remotion[0].sectionId;
        const outputPath = path.join(
          projectDir,
          "outputs",
          "sections",
          `${firstRemotionSectionId}.mp4`
        );
        applyDeterministicVideoOverlay(
          outputPath,
          extractRequestedHexColor(byFixType.remotion[0].text),
          onLog,
        );
      }

      if (resolvedAnnotationIds.size > 0) {
        const markResolved = db.prepare(
          "UPDATE annotations SET resolved = 1 WHERE id = ?"
        );
        for (const annotationId of resolvedAnnotationIds) {
          markResolved.run(annotationId);
        }
        onLog(`Marked ${resolvedAnnotationIds.size} annotations resolved.`);
      }
    }).catch((err) => {
      console.error(`[resolve-batch] runJob ${jobId} failed unexpectedly:`, err);
    }).finally(() => {
      releaseResolveSlot();
    });

    // 6. Return immediately (non-blocking)
    return NextResponse.json({ jobId }, { status: 200 });
  } catch (error) {
    console.error("Resolve batch failed:", error);
    return NextResponse.json(
      { error: "Internal Server Error" },
      { status: 500 }
    );
  }
}
