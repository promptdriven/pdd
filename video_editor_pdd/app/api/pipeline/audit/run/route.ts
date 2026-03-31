import { NextRequest, NextResponse } from "next/server";
import path from "path";
import fs from "fs";
import { registerExecutor, runPipelineStage } from "@/lib/jobs";
import {
  extractFrameAtTime,
  getCompositionDurationInFrames,
  getSectionDuration,
  renderStill,
} from "@/lib/render";
import { runClaudeAudit, runClaudeAuditWithTrace } from "@/lib/claude";
import { loadProject } from "@/lib/project";
import { createSseStream } from "@/lib/sse";
import {
  resolveSectionVisuals,
  resolveSpecAuditHints,
  type ResolvedSectionVisual,
} from "@/lib/composition-timing";
import {
  buildClaudeAuditSpecSnapshot,
  normalizeSpecForAudit,
} from "@/lib/audit-spec-normalization";
import {
  collectAuditImageEvidence,
  evaluateDeterministicTextAudit,
} from "@/lib/audit-evidence";
import {
  FRAME_SAMPLE_EPSILON_SECONDS,
  resolveAuditSampleWindow,
  resolveRenderedAuditSampleWindow,
} from "@/lib/audit-timing";
import { evaluateDeterministicGeometryAudit } from "@/lib/audit-geometry";
import { resolveSectionNarrativeTiming } from "@/lib/section-timing";
import {
  resolveSectionSpecDir,
  resolveSectionSpecFile,
} from "../_lib/spec-paths";
import { resolveSectionCompositionIds } from "@/app/api/pipeline/_lib/composition-manifest";
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
const GEOMETRY_DISCREPANCY_RE =
  /\b(center|centering|offset|drift|position|alignment|aligned|spacing|left|right|panel|split|x=|y=|undersized|oversized|size|width|height)\b/i;
const MAX_RENDERABLE_FRAME_RE =
  /highest frame that can be rendered is (\d+)/i;
const MEDIA_SAMPLE_EPSILON_SECONDS = 0.001;
const SUPSERSEDED_SPEC_TOMBSTONE_RE =
  /^\s*<!--\s*duplicate:\s*this spec has been superseded by\b/i;
const AUDIT_CLAUDE_MAX_CONCURRENT = Math.max(
  1,
  Number.parseInt(process.env.AUDIT_CLAUDE_MAX_CONCURRENT ?? "2", 10) || 2
);
const AUDIT_CLAUDE_MAX_RETRIES = Math.max(
  0,
  Number.parseInt(process.env.AUDIT_CLAUDE_MAX_RETRIES ?? "2", 10) || 2
);
const AUDIT_CLAUDE_RETRY_BASE_DELAY_MS =
  process.env.NODE_ENV === "test"
    ? 0
    : Math.max(
        0,
        Number.parseInt(process.env.AUDIT_CLAUDE_RETRY_BASE_DELAY_MS ?? "1500", 10) ||
          1500
      );

function createAsyncLimiter(maxConcurrent: number) {
  let activeCount = 0;
  const queue: Array<() => void> = [];

  const runNext = () => {
    if (activeCount >= maxConcurrent) {
      return;
    }
    const next = queue.shift();
    if (!next) {
      return;
    }
    activeCount++;
    next();
  };

  return async <T>(work: () => Promise<T>): Promise<T> =>
    new Promise<T>((resolve, reject) => {
      queue.push(() => {
        void work()
          .then(resolve, reject)
          .finally(() => {
            activeCount = Math.max(0, activeCount - 1);
            runNext();
          });
      });
      runNext();
    });
}

const runAuditClaudeLimited = createAsyncLimiter(AUDIT_CLAUDE_MAX_CONCURRENT);

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function isRecoverableClaudeAuditFailure(error: unknown): boolean {
  const message = error instanceof Error ? error.message : String(error ?? "");
  const normalized = message.toLowerCase();

  return (
    normalized.includes("failed to authenticate") ||
    normalized.includes("authentication_error") ||
    normalized.includes("invalid authentication credentials") ||
    normalized.includes("api error: 401") ||
    normalized.includes("api error: 429") ||
    normalized.includes("hit your limit") ||
    normalized.includes("rate limit") ||
    (normalized.includes("limit") && normalized.includes("reset")) ||
    normalized.includes("timeout") ||
    normalized.includes("timed out") ||
    normalized.includes("econnreset") ||
    normalized.includes("socket hang up")
  );
}

async function runClaudeAuditWithRetry(
  prompt: string,
  cwd: string,
  onLog: (line: string) => void,
  traceEnabled: boolean,
  specName: string
): Promise<{
  analysis: AnnotationAnalysis;
  trace: Awaited<ReturnType<typeof runClaudeAuditWithTrace>>["trace"] | null;
}> {
  return runAuditClaudeLimited(async () => {
    let attempt = 0;

    while (true) {
      try {
        if (traceEnabled) {
          const traced = await runClaudeAuditWithTrace(prompt, cwd, onLog);
          return { analysis: traced.analysis, trace: traced.trace };
        }

        const analysis = (await runClaudeAudit(
          prompt,
          cwd,
          onLog
        )) as AnnotationAnalysis;
        return { analysis, trace: null };
      } catch (error) {
        if (
          !isRecoverableClaudeAuditFailure(error) ||
          attempt >= AUDIT_CLAUDE_MAX_RETRIES
        ) {
          throw error;
        }

        const delayMs = AUDIT_CLAUDE_RETRY_BASE_DELAY_MS * (attempt + 1);
        const message =
          error instanceof Error ? error.message : String(error ?? "Unknown Claude failure");
        onLog(
          `[audit] Claude analysis unavailable for ${specName} (${message}). Retrying (${attempt + 1}/${AUDIT_CLAUDE_MAX_RETRIES})${delayMs > 0 ? ` in ${delayMs}ms` : ""}.`
        );
        if (delayMs > 0) {
          await sleep(delayMs);
        }
        attempt++;
      }
    }
  });
}

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

function clearStaleAuditStill(outputStill: string): void {
  if (!fs.existsSync(outputStill)) {
    return;
  }
  try {
    fs.unlinkSync(outputStill);
  } catch {
    // Best-effort cleanup; stale PNG removal should not abort the audit run.
  }
}

function clearSectionAuditArtifacts(sectionId: string): void {
  const sectionAuditDir = path.join(
    getProjectDir(),
    "outputs",
    "audit",
    sectionId
  );
  const sectionTraceDir = path.join(
    getProjectDir(),
    "outputs",
    "audit_traces",
    sectionId
  );

  for (const [dirPath, suffix] of [
    [sectionAuditDir, ".png"],
    [sectionTraceDir, ".json"],
  ] as const) {
    if (!fs.existsSync(dirPath)) {
      continue;
    }

    for (const entry of fs.readdirSync(dirPath)) {
      if (!entry.endsWith(suffix)) {
        continue;
      }

      try {
        fs.unlinkSync(path.join(dirPath, entry));
      } catch {
        // Ignore cleanup errors; the fresh render path below will still run.
      }
    }
  }
}

function extractMaxRenderableFrame(message: string): number | null {
  const match = message.match(MAX_RENDERABLE_FRAME_RE);
  if (!match) {
    return null;
  }

  const frame = Number(match[1]);
  return Number.isFinite(frame) && frame >= 0 ? frame : null;
}

async function clampSampleTimeToMediaDuration(
  mediaPath: string,
  sampleSeconds: number,
  onLog: (msg: string) => void
): Promise<number> {
  try {
    const durationSeconds = await getSectionDuration(mediaPath);
    if (!Number.isFinite(durationSeconds) || durationSeconds <= 0) {
      return sampleSeconds;
    }

    if (sampleSeconds < durationSeconds) {
      return sampleSeconds;
    }

    const clamped = Math.max(0, durationSeconds - MEDIA_SAMPLE_EPSILON_SECONDS);
    onLog(
      `[audit] Sample time ${sampleSeconds.toFixed(3)}s exceeded media duration ${durationSeconds.toFixed(3)}s; clamping to ${clamped.toFixed(3)}s`
    );
    return clamped;
  } catch {
    return sampleSeconds;
  }
}

function shouldSaveAuditTraces(): boolean {
  return process.env.VIDEO_EDITOR_SAVE_AUDIT_TRACES === "1";
}

function isSupersededSpecTombstone(content: string): boolean {
  const firstNonEmptyLine = content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .find((line) => line.length > 0);

  return Boolean(
    firstNonEmptyLine && SUPSERSEDED_SPEC_TOMBSTONE_RE.test(firstNonEmptyLine)
  );
}

function listActiveRawSpecFiles(specDir: string): string[] {
  if (!fs.existsSync(specDir)) {
    return [];
  }

  return fs
    .readdirSync(specDir)
    .filter((f) => f.endsWith(".md") && !f.startsWith("AUDIT_"))
    .filter((specFile) => {
      const specPath = path.join(specDir, specFile);
      try {
        return !isSupersededSpecTombstone(fs.readFileSync(specPath, "utf-8"));
      } catch {
        return true;
      }
    });
}

function clearStaleSectionAuditReports(
  section: Section,
  activeSpecNames: Set<string>,
  onLog: (msg: string) => void
): void {
  const specDir = resolveSectionSpecDir(section.specDir);
  if (!fs.existsSync(specDir)) {
    return;
  }

  for (const entry of fs.readdirSync(specDir)) {
    if (!entry.endsWith(".md") || !entry.startsWith("AUDIT_")) {
      continue;
    }

    const specName = path.basename(entry, ".md").replace(/^AUDIT_/, "");
    if (activeSpecNames.has(specName)) {
      continue;
    }

    const auditPath = path.join(specDir, entry);
    try {
      fs.unlinkSync(auditPath);
      onLog(`[audit] Removed stale audit report for non-renderable spec "${specName}"`);
    } catch {
      // Ignore cleanup errors; stale files should not block the active audit pass.
    }
  }
}

function writeAuditTrace(
  tracePath: string,
  payload: Record<string, unknown>
): void {
  fs.mkdirSync(path.dirname(tracePath), { recursive: true });
  fs.writeFileSync(tracePath, `${JSON.stringify(payload, null, 2)}\n`, "utf-8");
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
): "pass" | "warn" | "fail" | "skip" {
  if (!analysis || !analysis.severity) {
    return "skip";
  }

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

function shouldTrustDeterministicGeometry(
  analysis: AnnotationAnalysis
): boolean {
  const assessmentText = [
    analysis.technicalAssessment,
    ...(analysis.suggestedFixes ?? []),
  ]
    .join(" ")
    .toLowerCase();

  return GEOMETRY_DISCREPANCY_RE.test(assessmentText);
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

  if (visual.previewCompositionId && (visualType === "component" || visualType === "media")) {
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
  const rawSpecFiles = listActiveRawSpecFiles(specDir);
  const configuredCompositionIds = resolveSectionCompositionIds(section);
  const resolvedSectionVisuals = resolveSectionVisuals(
    getProjectDir(),
    section,
    configuredCompositionIds
  );
  const renderableVisuals =
    resolvedSectionVisuals.length > 0
      ? resolvedSectionVisuals
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
  clearSectionAuditArtifacts(section.id);
  clearStaleSectionAuditReports(
    section,
    new Set(renderableVisuals.map((visual) => visual.specName)),
    onLog
  );
  const previewFrameCountCache = new Map<string, Promise<number>>();

  const getPreviewFrameCount = async (
    compositionId: string,
    fallbackFrameCount: number
  ): Promise<number> => {
    if (!previewFrameCountCache.has(compositionId)) {
      previewFrameCountCache.set(
        compositionId,
        getCompositionDurationInFrames(compositionId)
      );
    }

    try {
      return Math.max(1, await previewFrameCountCache.get(compositionId)!);
    } catch (error) {
      previewFrameCountCache.delete(compositionId);
      const message =
        error instanceof Error ? error.message : "Unknown preview duration error";
      onLog(
        `[audit] Falling back to intrinsic preview duration for ${compositionId}: ${message}`
      );
      return Math.max(1, fallbackFrameCount);
    }
  };

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
    const claudeSpecSnapshot = buildClaudeAuditSpecSnapshot(
      specContent,
      project.outputResolution
    );
    const narrativeTiming = resolveSectionNarrativeTiming(getProjectDir(), section);
    const rawSampleWindow = resolveAuditSampleWindow(specContent, {
      sectionDurationSeconds: narrativeTiming.durationSeconds,
      fps,
      sectionOffsetSeconds: narrativeTiming.offsetSeconds,
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
      renderSource.kind === "preview-composition" ||
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
    const tracePath = path.join(
      getProjectDir(),
      "outputs",
      "audit_traces",
      section.id,
      `${specName}.json`
    );
    const auditPath = resolveSectionSpecFile(
      section.specDir,
      `AUDIT_${specName}.md`
    );

    if (renderSource.kind === "skip") {
      onLog(`[audit] Skipping standalone audit for ${section.id} (${specName}): ${renderSource.reason}`);
      writeAuditReport(auditPath, "skip", renderSource.reason);
      continue;
    }

    if (
      renderSource.kind !== "preview-composition" &&
      renderSource.kind !== "media-clip" &&
      renderSource.kind !== "section-composition" &&
      renderSource.kind !== "section-video"
    ) {
      throw new Error(`Unsupported audit render source: ${JSON.stringify(renderSource)}`);
    }

      try {
        clearStaleAuditStill(outputStill);

        if (renderSource.kind === "preview-composition") {
          const previewFrameCount = await getPreviewFrameCount(
            renderSource.compositionId,
            sampleWindow.intrinsicDurationFrames
          );
          const previewDurationFrames = Math.max(
            1,
            previewFrameCount
          );
          const sampleFrame = Math.max(
            0,
            Math.min(
              previewDurationFrames - 1,
              Math.round((previewDurationFrames - 1) * sampleWindow.normalizedSample)
            )
          );
          onLog(
            `[audit] Rendering preview still for ${section.id} (${specName}) from ${renderSource.compositionId} at frame ${sampleFrame} (${sampleWindow.source})`
          );
          try {
            await renderStill(renderSource.compositionId, sampleFrame, outputStill);
          } catch (err) {
            const message =
              err instanceof Error ? err.message : "Unknown audit render failure";
            const maxRenderableFrame = extractMaxRenderableFrame(message);
            if (
              maxRenderableFrame === null ||
              maxRenderableFrame >= sampleFrame
            ) {
              throw err;
            }

            onLog(
              `[audit] Preview still frame ${sampleFrame} exceeded ${renderSource.compositionId}; retrying at frame ${maxRenderableFrame}`
            );
            await renderStill(
              renderSource.compositionId,
              maxRenderableFrame,
              outputStill
            );
          }
        } else if (renderSource.kind === "media-clip") {
        onLog(
          `[audit] Extracting standalone media frame for ${section.id} (${specName}) at ${sampleWindow.intrinsicSampleSeconds.toFixed(3)}s`
        );
        const sampleSeconds = await clampSampleTimeToMediaDuration(
          renderSource.mediaPath,
          sampleWindow.intrinsicSampleSeconds,
          onLog
        );
        await extractFrameAtTime(
          renderSource.mediaPath,
          sampleSeconds,
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
      } else {
        const sampleSeconds = await clampSampleTimeToMediaDuration(
          renderSource.mediaPath,
          sampleWindow.sampleSeconds,
          onLog
        );
        onLog(
          `[audit] Extracting frame for ${section.id} (${specName}) at ${sampleSeconds.toFixed(3)}s from rendered video`
        );
        await extractFrameAtTime(
          renderSource.mediaPath,
          sampleSeconds,
          outputStill
        );
      }
    } catch (err) {
      clearStaleAuditStill(outputStill);
      const message =
        err instanceof Error ? err.message : "Unknown audit render failure";
      const summary = `Infrastructure error: Failed to render audit frame for ${specName}. ${message}`;
      onLog(`[audit] ${summary}`);
      writeAuditReport(auditPath, "skip", summary);
      continue;
    }

    try {
      // Claude analysis prompt
      const prompt = `
You are auditing a rendered video frame against a normalized spec snapshot.

Rules:
- Judge only the visible pixels in the frame.
- Do not inspect, infer, or comment on source code, implementation files, or repository contents.
- Do not speculate about stale renders or code state.
- Fail only for visible mismatches in the sampled frame.
- Treat spatial requirements semantically rather than as exact pixel arithmetic.
- The spec snapshot below has been rewritten into relative layout language for your review.
- If the snapshot includes a "Structured Visual Contract (authoritative)" section, treat that structured contract as the source of truth over conflicting prose.

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
- Claude-facing spec snapshot for audit:
${claudeSpecSnapshot}
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

      const traceEnabled = shouldSaveAuditTraces();
      const { analysis, trace: trace } = await runClaudeAuditWithRetry(
        prompt,
        path.dirname(outputStill),
        onLog,
        traceEnabled,
        specName
      );
      let verdict = classifyAuditVerdict(analysis, { auditHints });
      let summary =
        analysis.technicalAssessment ??
        (verdict === "skip"
          ? "Audit model returned no parseable assessment for this frame."
          : "Audit completed without a detailed technical assessment.");
      let deterministicGeometry: ReturnType<typeof evaluateDeterministicGeometryAudit> =
        null;
      let deterministicText = null;

      if (verdict !== "pass" && shouldTrustDeterministicGeometry(analysis)) {
        deterministicGeometry = evaluateDeterministicGeometryAudit(
          specContent,
          outputStill
        );
        if (deterministicGeometry?.verdict === "pass") {
          verdict = "pass";
          summary = deterministicGeometry.summary;
        }
      }

      if (verdict !== "pass") {
        const imageEvidence = await collectAuditImageEvidence(outputStill);
        deterministicText = evaluateDeterministicTextAudit(
          analysis,
          auditHints,
          imageEvidence
        );
        if (deterministicText) {
          verdict = deterministicText.verdict;
          summary = deterministicText.summary;
        }
      }

      if (!summary || !summary.trim()) {
        summary =
          verdict === "skip"
            ? "Audit model returned no parseable assessment for this frame."
            : "Audit completed without a detailed technical assessment.";
      }

      if (verdict === "pass") passCount++;
      else if (verdict === "warn") warnCount++;
      else if (verdict === "fail") failCount++;
      writeAuditReport(auditPath, verdict, summary);
      if (traceEnabled && trace) {
        writeAuditTrace(tracePath, {
          sectionId: section.id,
          specName,
          specPath,
          auditPath,
          framePath: outputStill,
          renderSource,
          sampleWindow,
          normalizedSpecSnapshot: normalizedSpecContent,
          claudeSpecSnapshot,
          auditHints,
          analysis,
          verdict,
          summary,
          deterministicGeometry,
          deterministicText,
          trace,
          prompt,
        });
      }
    } catch (err) {
      const message =
        err instanceof Error ? err.message : "Unknown audit analysis failure";
      const summary = `Infrastructure error: Failed to analyze audit frame for ${specName}. ${message}`;
      onLog(`[audit] ${summary}`);
      if (isRecoverableClaudeAuditFailure(err)) {
        writeAuditReport(auditPath, "skip", summary);
        continue;
      }
      failCount++;
      writeAuditReport(auditPath, "fail", summary);
      continue;
    }
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
