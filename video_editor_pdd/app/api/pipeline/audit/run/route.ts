import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import { extractFrameAtTime, renderStill } from "@/lib/render";
import { runClaudeAudit } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import { createSseStream } from "@/lib/sse";
import {
  resolveSectionVisuals,
  type ResolvedSectionVisual,
} from "@/lib/composition-timing";
import { normalizeSpecForAudit } from "@/lib/audit-spec-normalization";
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
type AuditVisualType = "component" | "media" | "hybrid" | "spec";
type AuditRenderSource =
  | {
      kind: "preview-composition";
      visualType: AuditVisualType;
      compositionId: string;
    }
  | {
      kind: "media-clip" | "section-video";
      visualType: AuditVisualType;
      mediaPath: string;
    }
  | {
      kind: "section-composition";
      visualType: AuditVisualType;
      compositionId: string;
    }
  | {
      kind: "skip";
      visualType: AuditVisualType;
      reason: string;
    };

const DEFAULT_PREVIEW_DURATION_FRAMES = 150;

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

function resolveVisualType(visual: Pick<ResolvedSectionVisual, "hasComponent" | "hasExplicitMedia">): AuditVisualType {
  if (visual.hasComponent && visual.hasExplicitMedia) {
    return "hybrid";
  }
  if (visual.hasComponent) {
    return "component";
  }
  if (visual.hasExplicitMedia) {
    return "media";
  }
  return "spec";
}

function resolveVisualMediaAssetPath(
  projectDir: string,
  visual: Pick<ResolvedSectionVisual, "mediaReferences" | "stagedAssetPath">
): string | null {
  const candidates = new Set<string>();

  if (visual.stagedAssetPath) {
    candidates.add(visual.stagedAssetPath);
  }

  for (const mediaReference of visual.mediaReferences ?? []) {
    if (path.isAbsolute(mediaReference)) {
      candidates.add(mediaReference);
      continue;
    }

    const normalized = mediaReference
      .replace(/\\/g, "/")
      .replace(/^public\//, "")
      .replace(/^\//, "");

    candidates.add(path.join(projectDir, "remotion", "public", normalized));
    candidates.add(path.join(projectDir, normalized));
    candidates.add(
      path.join(projectDir, "outputs", "veo", path.basename(normalized))
    );
  }

  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }

  return null;
}

function writeAuditReport(
  auditPath: string,
  verdict: "pass" | "fail" | "skip" | "warn",
  summary: string
): void {
  const auditReport = `## Verdict\n${verdict}\n## Summary\n${summary}\n`;
  fs.mkdirSync(path.dirname(auditPath), { recursive: true });
  fs.writeFileSync(auditPath, auditReport, "utf-8");
}

function resolveAuditRenderSource(
  projectDir: string,
  section: Section,
  visual: Pick<
    ResolvedSectionVisual,
    | "hasComponent"
    | "hasExplicitMedia"
    | "requiresCompositedAudit"
    | "previewCompositionId"
    | "mediaReferences"
    | "stagedAssetPath"
  >,
  renderedVideoPath: string | null,
  canRenderFreshStill: boolean
): AuditRenderSource {
  const visualType = resolveVisualType(visual);

  if (visualType === "component" && visual.previewCompositionId) {
    return {
      kind: "preview-composition",
      visualType,
      compositionId: visual.previewCompositionId,
    };
  }

  if (visualType === "media") {
    if (visual.requiresCompositedAudit) {
      return {
        kind: "skip",
        visualType,
        reason:
          "Standalone audit skipped because this media spec requires composited overlays or UI that cannot be audited from a bare clip.",
      };
    }

    const mediaPath = resolveVisualMediaAssetPath(projectDir, visual);
    if (mediaPath) {
      return {
        kind: "media-clip",
        visualType,
        mediaPath,
      };
    }

    return {
      kind: "skip",
      visualType,
      reason:
        "Standalone audit skipped because the staged media clip for this spec could not be resolved.",
    };
  }

  if (visualType === "hybrid") {
    return {
      kind: "skip",
      visualType,
      reason:
        "Standalone audit skipped because this visual mixes component rendering with media references that are not auditable as a single standalone source.",
    };
  }

  if (canRenderFreshStill && section.compositionId) {
    return {
      kind: "section-composition",
      visualType,
      compositionId: section.compositionId,
    };
  }

  if (renderedVideoPath) {
    return {
      kind: "section-video",
      visualType,
      mediaPath: renderedVideoPath,
    };
  }

  if (section.compositionId) {
    return {
      kind: "section-composition",
      visualType,
      compositionId: section.compositionId,
    };
  }

  return {
    kind: "skip",
    visualType,
    reason:
      "Standalone audit skipped because there is no renderable composition or staged media clip for this spec.",
  };
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
            visual,
          }))
      : rawSpecFiles.map((specFile) => ({
          specPath: path.join(specDir, specFile),
          specName: path.basename(specFile, ".md"),
          visual: {
            id: path.basename(specFile, ".md"),
            specBaseName: path.basename(specFile, ".md"),
            specPath: path.join(specDir, specFile),
            hasComponent: false,
            hasExplicitMedia: false,
            requiresCompositedAudit: false,
            mediaReferences: [],
          } satisfies ResolvedSectionVisual,
        }));
  const project = loadProject();
  const fps = project.render.fps ?? 30;
  const canRenderFreshStill =
    configuredCompositionIds.length > 0 && Boolean(section.compositionId);
  const renderedVideoPath = resolveSectionRenderedVideoPath(section);

  let passCount = 0;
  let failCount = 0;

  for (const visual of renderableVisuals) {
    const specPath = visual.specPath;
    const specName = visual.specName;
    const specContent = fs.readFileSync(specPath, "utf-8");
    const normalizedSpecContent = normalizeSpecForAudit(
      specContent,
      project.outputResolution
    );
    const rawSampleWindow = resolveAuditSampleWindow(specContent, {
      sectionDurationSeconds: section.durationSeconds,
      fps,
      sectionOffsetSeconds: section.offsetSeconds ?? 0,
    });
    const renderedSampleWindow =
      Array.isArray(section.compositions) && section.compositions.length > 0
        ? resolveRenderedAuditSampleWindow(specContent, {
            projectDir: getProjectDir(),
            specPath,
            section,
            sectionDurationSeconds: section.durationSeconds,
            fps,
          })
        : rawSampleWindow;
    const renderSource = resolveAuditRenderSource(
      getProjectDir(),
      section,
      visual.visual,
      renderedVideoPath,
      canRenderFreshStill
    );
    const sampleWindow =
      renderSource.kind === "section-composition" ||
      renderSource.kind === "section-video"
        ? renderedSampleWindow
        : rawSampleWindow;

    const outputStill = path.join(
      getProjectDir(),
      "outputs",
      "audit",
      section.id,
      `${specName}_frame.png`
    );
    fs.mkdirSync(path.dirname(outputStill), { recursive: true });
    const auditPath = resolveSectionSpecFile(
      section.specDir,
      `AUDIT_${specName}.md`
    );

    if (renderSource.kind === "preview-composition") {
      const sampleFrame = Math.min(
        DEFAULT_PREVIEW_DURATION_FRAMES - 1,
        Math.max(0, sampleWindow.intrinsicSampleFrame)
      );
      onLog(
        `[audit] Rendering preview still for ${section.id} (${specName}) from ${renderSource.compositionId} at frame ${sampleFrame} (${sampleWindow.source})`
      );
      await renderStill(renderSource.compositionId, sampleFrame, outputStill);
    } else if (renderSource.kind === "media-clip") {
      onLog(
        `[audit] Extracting standalone media frame for ${section.id} (${specName}) at ${sampleWindow.intrinsicSampleSeconds.toFixed(3)}s`
      );
      await extractFrameAtTime(
        renderSource.mediaPath,
        sampleWindow.intrinsicSampleSeconds,
        outputStill
      );
    } else if (renderSource.kind === "section-composition") {
      const sectionFrameCount = Math.max(1, Math.floor(section.durationSeconds * fps));
      const sampleFrame = Math.min(
        sectionFrameCount - 1,
        Math.max(0, Math.floor(sampleWindow.sampleSeconds * fps))
      );
      onLog(
        `[audit] Rendering fresh still for ${section.id} (${specName}) at frame ${sampleFrame} (${sampleWindow.source})`
      );
      await renderStill(renderSource.compositionId, sampleFrame, outputStill);
    } else if (renderSource.kind === "section-video") {
      onLog(
        `[audit] Extracting frame for ${section.id} (${specName}) at ${sampleWindow.sampleSeconds.toFixed(3)}s from rendered video`
      );
      await extractFrameAtTime(
        renderSource.mediaPath,
        sampleWindow.sampleSeconds,
        outputStill
      );
    } else if (renderSource.kind === "skip") {
      onLog(`[audit] Skipping standalone audit for ${section.id} (${specName}): ${renderSource.reason}`);
      writeAuditReport(auditPath, "skip", renderSource.reason);
      continue;
    } else {
      throw new Error(`Unsupported audit render source: ${JSON.stringify(renderSource)}`);
    }

    // Claude analysis prompt
    const prompt = `
You are auditing a rendered video frame against a normalized spec snapshot.

Rules:
- Judge only the visible pixels in the frame.
- Do not inspect, infer, or comment on source code, implementation files, or repository contents.
- Do not speculate about stale renders or code state.
- Fail only for visible mismatches in the sampled frame.

- Audit spec name: ${path.basename(specPath)}
- Audit render source: ${renderSource.kind}
- Render resolution: ${project.outputResolution.width}x${project.outputResolution.height}
- Audit visual type: ${renderSource.visualType}
- Sample window: ${sampleWindow.startSeconds.toFixed(3)}s - ${sampleWindow.endSeconds.toFixed(3)}s (${sampleWindow.source})
- Sample time (section-local): ${sampleWindow.sampleSeconds.toFixed(3)}s
- Sample time (intrinsic visual): ${sampleWindow.intrinsicSampleSeconds.toFixed(3)}s / ${sampleWindow.intrinsicDurationSeconds.toFixed(3)}s
- Sample frame (intrinsic visual): ${sampleWindow.intrinsicSampleFrame} / ${sampleWindow.intrinsicDurationFrames}
- Sample progress within intrinsic visual: ${(sampleWindow.normalizedSample * 100).toFixed(1)}%
- Normalized spec snapshot for audit:
${normalizedSpecContent}
- Frame PNG: ./${path.basename(outputStill)}

Read the frame PNG and compare it against the normalized spec snapshot above. Return JSON matching AnnotationAnalysis:
{ severity, fixType, technicalAssessment, suggestedFixes, confidence }

Use severity="pass" if the frame fully satisfies the spec.
Use severity="minor" for subtle, non-material differences that do not meaningfully break the intended visual.
Reserve severity="major" or "critical" for clearly missing, wrong, or materially broken visuals.
`;

    const analysis = (await runClaudeAudit(
      prompt,
      path.dirname(outputStill),
      onLog
    )) as AnnotationAnalysis;

    const verdict =
      analysis.severity === "pass"
        ? "pass"
        : analysis.severity === "minor"
          ? "warn"
          : "fail";
    if (verdict === "pass") passCount++;
    else if (verdict === "fail") failCount++;
    writeAuditReport(auditPath, verdict, analysis.technicalAssessment);
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
