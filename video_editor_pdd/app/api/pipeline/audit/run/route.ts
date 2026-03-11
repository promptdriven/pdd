import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { extractFrameAtTime, renderStill } from "@/lib/render";
import { runClaudeAnalysis } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import { createSseStream } from "@/lib/sse";
import { resolveSectionVisuals } from "@/lib/composition-timing";
import {
  resolveAuditSampleWindow,
  resolveRenderedAuditSampleWindow,
} from "@/lib/audit-timing";
import {
  resolveSectionSpecDir,
  resolveSectionSpecFile,
} from "../_lib/spec-paths";
import type { AnnotationAnalysis, Section, SseSend } from "@/lib/types";
import { getProjectDir } from "@/lib/projects";

// --- app/api/pipeline/audit/run/route.ts ---

type AuditSectionStatus = "running" | "done" | "error";

function resolveSectionRenderedVideoPath(section: Section): string | null {
  const candidates = new Set<string>();

  if (section.videoFile) {
    if (path.isAbsolute(section.videoFile)) {
      candidates.add(section.videoFile);
    } else {
      candidates.add(path.join(getProjectDir(), section.videoFile));
      candidates.add(
        path.join(getProjectDir(), "outputs", "sections", path.basename(section.videoFile))
      );
    }
  }

  candidates.add(path.join(getProjectDir(), "outputs", "sections", `${section.id}.mp4`));

  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }

  return null;
}

async function auditSection(
  section: Section,
  send: SseSend,
  onLog: (msg: string) => void
): Promise<{ passCount: number; failCount: number }> {
  const specDir = resolveSectionSpecDir(section.specDir);
  const rawSpecFiles = fs.existsSync(specDir)
    ? fs
        .readdirSync(specDir)
        .filter((f) => f.endsWith(".md") && !f.startsWith("AUDIT_"))
    : [];
  const configuredCompositionIds = (section.compositions ?? [])
    .map((composition) =>
      typeof composition === "string" ? composition : composition?.id
    )
    .filter((compositionId): compositionId is string => Boolean(compositionId));
  const renderableVisuals =
    configuredCompositionIds.length > 0
      ? resolveSectionVisuals(
          getProjectDir(),
          section,
          configuredCompositionIds
        )
          .filter((visual) => Boolean(visual.specPath))
          .map((visual) => ({
            specPath: visual.specPath as string,
            specName: visual.specBaseName,
          }))
      : rawSpecFiles.map((specFile) => ({
          specPath: path.join(specDir, specFile),
          specName: path.basename(specFile, ".md"),
        }));
  const fps = loadProject().render.fps ?? 30;

  let passCount = 0;
  let failCount = 0;

  for (const visual of renderableVisuals) {
    const specPath = visual.specPath;
    const specName = visual.specName;
    const specContent = fs.readFileSync(specPath, "utf-8");
    const sampleWindow =
      Array.isArray(section.compositions) && section.compositions.length > 0
        ? resolveRenderedAuditSampleWindow(specContent, {
            projectDir: getProjectDir(),
            specPath,
            section,
            sectionDurationSeconds: section.durationSeconds,
            fps,
          })
        : resolveAuditSampleWindow(specContent, {
            sectionDurationSeconds: section.durationSeconds,
            fps,
          });
    const renderedVideoPath = resolveSectionRenderedVideoPath(section);

    const outputStill = path.join(
      "outputs",
      "audit",
      section.id,
      `${specName}_frame.png`
    );
    fs.mkdirSync(path.dirname(outputStill), { recursive: true });

    if (renderedVideoPath) {
      onLog(
        `[audit] Extracting frame for ${section.id} (${specName}) at ${sampleWindow.sampleSeconds.toFixed(3)}s from rendered video`
      );
      await extractFrameAtTime(
        renderedVideoPath,
        sampleWindow.sampleSeconds,
        outputStill
      );
    } else {
      const sectionFrameCount = Math.max(1, Math.floor(section.durationSeconds * fps));
      const sampleFrame = Math.min(
        sectionFrameCount - 1,
        Math.max(0, Math.floor(sampleWindow.sampleSeconds * fps))
      );
      onLog(
        `[audit] Rendering still for ${section.id} (${specName}) at frame ${sampleFrame} (${sampleWindow.source})`
      );
      await renderStill(section.compositionId, sampleFrame, outputStill);
    }

    // Claude analysis prompt
    const prompt = `
You are auditing a video frame against a spec.

- Spec file: ${specPath}
- Frame PNG: ${outputStill}

Read both files and return JSON matching AnnotationAnalysis:
{ severity, fixType, technicalAssessment, suggestedFixes, confidence }

Use severity="pass" if the frame fully satisfies the spec.
`;

    const analysis = (await runClaudeAnalysis(
      prompt,
      onLog
    )) as AnnotationAnalysis;

    const verdict = analysis.severity === "pass" ? "pass" : "fail";
    if (verdict === "pass") passCount++;
    else failCount++;

    const auditReport = `## Verdict\n${verdict}\n## Summary\n${analysis.technicalAssessment}\n`;

    const auditPath = resolveSectionSpecFile(
      section.specDir,
      `AUDIT_${specName}.md`
    );
    fs.mkdirSync(path.dirname(auditPath), { recursive: true });
    fs.writeFileSync(auditPath, auditReport, "utf-8");
  }

  return { passCount, failCount };
}

// Register executor at module load time
registerExecutor("audit", (params, send) => {
  return async (onLog) => {
    const config = loadProject();
    const sectionIds = Array.isArray(params.sections)
      ? (params.sections as string[])
      : config.sections.map((s) => s.id);

    const sections = config.sections.filter((s) =>
      sectionIds.includes(s.id)
    );

    await Promise.all(
      sections.map(async (section) => {
        send({
          type: "audit-section",
          sectionId: section.id,
          status: "running",
          passCount: 0,
          failCount: 0,
        });

        try {
          const { passCount, failCount } = await auditSection(
            section,
            send,
            onLog
          );

          send({
            type: "audit-section",
            sectionId: section.id,
            status: "done",
            passCount,
            failCount,
          });
        } catch (err) {
          console.error(err);
          send({
            type: "audit-section",
            sectionId: section.id,
            status: "error",
            passCount: 0,
            failCount: 0,
          });
        }
      })
    );
  };
});

export async function POST(request: NextRequest) {
  const body = await request.json().catch(() => ({}));
  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage(
        "audit",
        { sections: body.sections },
        send
      );
      send({ type: "job", jobId });
      done();
    } catch (err) {
      error(err instanceof Error ? err.message : "Unknown error");
    }
  })();

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}

// NOTE: The GET handler for /api/pipeline/audit/results lives in
// app/api/pipeline/audit/results/route.ts
