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
  resolveSpecAuditHints,
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
const DECORATIVE_DISCREPANCY_RE =
  /\b(glow|shadow|blur|bloom|rule|separator|trail|streak|opacity|gradient|halo|flare)\b/i;
const MILD_DIFFERENCE_RE =
  /\b(slight|slightly|subtle|subtly|minor|roughly|approximately|faint|dimmer|softer|nearly|almost|just|beginning|starting)\b/i;
const LAYOUT_DISCREPANCY_RE =
  /\b(center|centering|offset|drift|position|alignment|aligned|spacing|upward|downward|left|right)\b/i;
const TRANSITION_DISCREPANCY_RE =
  /\b(transition|fade|fading|appearing|emerging|stagger|timing|phase|beginning to appear|starting to appear|not yet fully visible|not fully visible)\b/i;
const HARD_PROBLEM_RE =
  /\b(missing|wrong subject|wrong scene|off-screen|outside the frame|clipped|cut off|cropped|illegible|unreadable|completely absent|not visible|invisible|far from|significantly|materially)\b/i;

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

function formatAuditHints(
  visual: Pick<ResolvedSectionVisual, "auditHints">,
): string {
  const hints = visual.auditHints;
  const lines = ["Audit hints:"];

  lines.push(
    `- Critical elements: ${
      hints.criticalElements.length > 0
        ? hints.criticalElements.join(", ")
        : "none inferred from spec"
    }`
  );
  lines.push(
    `- Decorative elements that may vary slightly without failing: ${
      hints.decorativeElements.length > 0
        ? hints.decorativeElements.join(", ")
        : "none inferred from spec"
    }`
  );
  lines.push(
    `- Layout intent: ${
      hints.layoutKeywords.length > 0
        ? hints.layoutKeywords.join(", ")
        : "no explicit layout keywords inferred"
    }`
  );
  lines.push(
    `- Animation phases: ${
      hints.transitionWindows.length > 0
        ? hints.transitionWindows
            .map(
              (window) =>
                `${window.startFrame}-${window.endFrame}: ${window.description}`
            )
            .join(" | ")
        : "none inferred from spec"
    }`
  );

  return lines.join("\n");
}

function classifyAuditVerdict(
  analysis: AnnotationAnalysis,
  visual: Pick<ResolvedSectionVisual, "auditHints">
): "pass" | "warn" | "fail" {
  if (analysis.severity === "pass") {
    return "pass";
  }

  if (analysis.severity !== "minor") {
    return "fail";
  }

  const assessmentText = [
    analysis.technicalAssessment,
    ...(analysis.suggestedFixes ?? []),
  ]
    .join(" ")
    .toLowerCase();

  if (HARD_PROBLEM_RE.test(assessmentText)) {
    return "warn";
  }

  const decorativeTerms = visual.auditHints.decorativeElements
    .map((element) => element.toLowerCase())
    .filter(Boolean);
  const mentionsDecorativeDifference =
    DECORATIVE_DISCREPANCY_RE.test(assessmentText) ||
    decorativeTerms.some((term) => assessmentText.includes(term));
  const mentionsLayoutDifference = LAYOUT_DISCREPANCY_RE.test(assessmentText);
  const mentionsTransitionDifference = TRANSITION_DISCREPANCY_RE.test(
    assessmentText
  );
  const mentionsMildDifference = MILD_DIFFERENCE_RE.test(assessmentText);

  if (
    (mentionsDecorativeDifference && mentionsMildDifference) ||
    (mentionsLayoutDifference &&
      mentionsMildDifference &&
      visual.auditHints.layoutKeywords.length > 0) ||
    (mentionsTransitionDifference &&
      visual.auditHints.transitionWindows.length > 0)
  ) {
    return "pass";
  }

  return "warn";
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
    | "auditHints"
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
      if (canRenderFreshStill && section.compositionId) {
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
          "Standalone audit skipped because this media spec requires composited overlays or UI, but no composed section render is available.",
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
    if (visual.previewCompositionId) {
      return {
        kind: "preview-composition",
        visualType,
        compositionId: visual.previewCompositionId,
      };
    }

    if (canRenderFreshStill && section.compositionId) {
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
        "Standalone audit skipped because this visual mixes component rendering with media references, but no composed render source is available.",
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
): Promise<{ passCount: number; warnCount: number; failCount: number }> {
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
            auditHints: {
              criticalElements: [],
              decorativeElements: [],
              layoutKeywords: [],
              transitionWindows: [],
            },
          } satisfies ResolvedSectionVisual,
        }));
  const project = loadProject();
  const fps = project.render.fps ?? 30;
  const canRenderFreshStill =
    configuredCompositionIds.length > 0 && Boolean(section.compositionId);
  const renderedVideoPath = resolveSectionRenderedVideoPath(section);

  let passCount = 0;
  let warnCount = 0;
  let failCount = 0;

  for (const visual of renderableVisuals) {
    const specPath = visual.specPath;
    const specName = visual.specName;
    const specContent = fs.readFileSync(specPath, "utf-8");
    const auditHints =
      visual.visual.auditHints.criticalElements.length > 0 ||
      visual.visual.auditHints.decorativeElements.length > 0 ||
      visual.visual.auditHints.layoutKeywords.length > 0 ||
      visual.visual.auditHints.transitionWindows.length > 0
        ? visual.visual.auditHints
        : resolveSpecAuditHints(specContent);
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
${formatAuditHints({ auditHints })}
- Normalized spec snapshot for audit:
${normalizedSpecContent}
- Frame PNG: ./${path.basename(outputStill)}

Read the frame PNG and compare it against the normalized spec snapshot above. Return JSON matching AnnotationAnalysis:
{ severity, fixType, technicalAssessment, suggestedFixes, confidence }

Use severity="pass" if the frame fully satisfies the spec.
Treat small layout drift within roughly 3% of the frame width/height, or slight centering variance that preserves the intended composition, as pass.
Treat subtle differences in glow, shadow, blur, rule thickness, or opacity as pass when the intended visual effect is still clearly present.
Treat timing that is within the same intended animation phase and visually reads correctly as pass.
Use severity="minor" for subtle, non-material differences that do not meaningfully break the intended visual.
Use severity="minor" only when a discrepancy would likely be noticeable during normal playback or would matter to a reviewer comparing the frame carefully.
Reserve severity="major" or "critical" for clearly missing, wrong, or materially broken visuals.
`;

    const analysis = (await runClaudeAudit(
      prompt,
      path.dirname(outputStill),
      onLog
    )) as AnnotationAnalysis;

    const verdict = classifyAuditVerdict(analysis, { auditHints });
    if (verdict === "pass") passCount++;
    else if (verdict === "warn") warnCount++;
    else if (verdict === "fail") failCount++;
    writeAuditReport(auditPath, verdict, analysis.technicalAssessment);
  }

  return { passCount, warnCount, failCount };
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
          warnCount: 0,
          failCount: 0,
        });

        try {
          const { passCount, warnCount, failCount } = await auditSection(
            section,
            send,
            onLog
          );

          send({
            type: "audit-section",
            sectionId: section.id,
            status: "done",
            passCount,
            warnCount,
            failCount,
          });
        } catch (err) {
          console.error(err);
          send({
            type: "audit-section",
            sectionId: section.id,
            status: "error",
            passCount: 0,
            warnCount: 0,
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
