import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { extractFrameAtTime, renderStill } from "@/lib/render";
import { runClaudeAnalysis } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import { createSseStream } from "@/lib/sse";
import { resolveAuditSampleWindow } from "@/lib/audit-timing";
import {
  resolveSectionSpecDir,
  resolveSectionSpecFile,
} from "../_lib/spec-paths";
import type { AnnotationAnalysis, Section, SseSend } from "@/lib/types";

// --- app/api/pipeline/audit/run/route.ts ---

type AuditSectionStatus = "running" | "done" | "error";

function resolveSectionRenderedVideoPath(section: Section): string | null {
  const candidates = new Set<string>();

  if (section.videoFile) {
    if (path.isAbsolute(section.videoFile)) {
      candidates.add(section.videoFile);
    } else {
      candidates.add(path.join(process.cwd(), section.videoFile));
      candidates.add(
        path.join(process.cwd(), "outputs", "sections", path.basename(section.videoFile))
      );
    }
  }

  candidates.add(path.join(process.cwd(), "outputs", "sections", `${section.id}.mp4`));

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
  const specFiles = fs.existsSync(specDir)
    ? fs
        .readdirSync(specDir)
        .filter((f) => f.endsWith(".md") && !f.startsWith("AUDIT_"))
    : [];
  const fps = loadProject().render.fps ?? 30;

  let passCount = 0;
  let failCount = 0;

  for (const specFile of specFiles) {
    const specPath = path.join(specDir, specFile);
    const specName = path.basename(specFile, ".md");
    const specContent = fs.readFileSync(specPath, "utf-8");
    const sampleWindow = resolveAuditSampleWindow(specContent, {
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
