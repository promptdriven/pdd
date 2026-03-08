// app/api/sections/[id]/resolve-batch/route.ts
import { NextResponse } from "next/server";
import path from "path";
import { execSync } from "child_process";
import { getDb } from "@/lib/db";
import { runClaudeFix } from "@/lib/claude";
import { createJob, runJob } from "@/lib/jobs";
import { renderSection } from "@/lib/render";
import { loadProject, getSection } from "@/lib/project";
import { isGitAvailable, preFixCommit, fixCommit } from "@/lib/git";
import type { Annotation } from "@/lib/types";

export const dynamic = "force-dynamic";

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
          `SELECT * FROM annotations WHERE sectionId = ? AND id IN (${placeholders}) AND resolved = 0 ORDER BY timestamp ASC`
        )
        .all(sectionId, ...annotationIds) as Array<Record<string, unknown>>;
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

    // 5. Fire-and-forget execution
    void runJob(jobId, async (onLog) => {
      const byFixType: Record<string, Annotation[]> = {
        remotion: [],
        veo: [],
        tts: [],
        manual: [],
        none: [],
      };

      for (const ann of annotations) {
        const fixType = ann.analysis?.fixType ?? "manual";
        if (byFixType[fixType]) byFixType[fixType].push(ann);
      }

      // Pre-fix git snapshot
      const gitAvail = isGitAvailable();
      if (gitAvail) {
        const preSha = preFixCommit(sectionId, jobId);
        if (preSha) onLog(`Pre-fix snapshot committed: ${preSha.slice(0, 8)}`);
      }

      // Remotion fixes via Claude
      for (const ann of byFixType.remotion) {
        onLog(`Running Claude fix for annotation ${ann.id}`);
        await runClaudeFix(
          buildRemotionPrompt(ann),
          "remotion/src/remotion/",
          onLog
        );

        // Git commit after fix
        if (gitAvail) {
          const sha = fixCommit(ann.id, ann.text.slice(0, 50));
          if (sha) {
            onLog(`Fix committed: ${sha.slice(0, 8)}`);
            db.prepare("UPDATE annotations SET fixCommitSha = ? WHERE id = ?").run(sha, ann.id);
          }
        }
      }

      // Veo fixes (placeholder)
      for (const ann of byFixType.veo) {
        onLog(`Queued Veo regeneration for annotation ${ann.id} (pending)`);
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
      const remotionDir = path.join(process.cwd(), "remotion");
      onLog("Rebuilding Remotion bundle...");
      execSync("npx remotion bundle src/index.ts --out build", {
        cwd: remotionDir,
        stdio: "pipe",
        timeout: 120_000,
      });
      onLog("Bundle rebuilt.");

      // Render the affected section
      const project = loadProject();
      const section = getSection(sectionId, project);
      const compositionId = section?.compositionId ?? `${toPascalCase(sectionId)}Section`;
      const outputPath = path.join("outputs", "sections", `${sectionId}.mp4`);
      onLog(`Rendering section ${sectionId} (${compositionId}) → ${outputPath}`);
      await renderSection(compositionId, outputPath, (progress) => {
        onLog.progress?.(progress.percent);
        onLog(progress.message);
      });
    }).catch((err) => {
      console.error(`[resolve-batch] runJob ${jobId} failed unexpectedly:`, err);
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
