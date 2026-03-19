import fs from "fs";
import path from "path";

import {
  resolveSectionVisuals,
  resolveSectionVisualTimings,
} from "./composition-timing";
import { resolveSectionNarrativeTiming } from "./section-timing";
import {
  normalizeSpecTimestampRangeToSection,
  parseSpecTimestampRange,
} from "./spec-timestamp";
import type { Section } from "./types";

type ResolveOptions = {
  sectionDurationSeconds: number;
  fps: number;
  sectionOffsetSeconds?: number;
};

type RenderedResolveOptions = {
  projectDir: string;
  specPath: string;
  section: Section;
  fps: number;
  sectionSpecFiles?: string[];
  sectionDurationSeconds?: number;
};

type AuditSampleWindow = {
  source: "timestamp" | "frame-range" | "fallback";
  startSeconds: number;
  endSeconds: number;
  sampleSeconds: number;
  intrinsicDurationSeconds: number;
  intrinsicSampleSeconds: number;
  intrinsicDurationFrames: number;
  intrinsicSampleFrame: number;
  normalizedSample: number;
};

type FrameRange = {
  start: number;
  end: number;
  label: string;
};

const FRAME_RANGE_RE =
  /Frames?\s+(\d+)\s*-\s*(\d+)(?:\s*\([^)]*\))?\s*:\s*(.+)$/i;
const HOLD_RE = /(hold|static|steady|full opacity|final|remains on screen|remains steady|all elements static)/i;
const FRAME_SAMPLE_EPSILON_SECONDS = 0.0005;

const clampEndToSection = (endSeconds: number, sectionDurationSeconds: number): number =>
  Math.min(endSeconds, Math.max(sectionDurationSeconds - 0.001, 0));

const parseTimestampWindow = (
  content: string,
  options: ResolveOptions
): { start: number; end: number } | null => {
  const range = parseSpecTimestampRange(content);
  if (!range) {
    return null;
  }

  const normalizedRange = normalizeSpecTimestampRangeToSection(
    range,
    options.sectionDurationSeconds,
    options.sectionOffsetSeconds ?? 0
  );

  const sectionGuardSeconds = 1 / Math.max(options.fps, 1);
  const overlapsSectionWindow =
    normalizedRange.endSeconds > 0 &&
    normalizedRange.startSeconds < options.sectionDurationSeconds + sectionGuardSeconds;

  if ((options.sectionOffsetSeconds ?? 0) > 0 && !overlapsSectionWindow) {
    return null;
  }

  return {
    start: normalizedRange.startSeconds,
    end: normalizedRange.endSeconds,
  };
};

const parseFrameRanges = (content: string): FrameRange[] =>
  content
    .split(/\r?\n/)
    .map((line) => line.trim())
    .map((line) => line.replace(/^\d+\.\s*/, "").replace(/\*\*/g, ""))
    .map((line) => {
      const match = line.match(FRAME_RANGE_RE);
      if (!match) {
        return null;
      }

      return {
        start: Number(match[1]),
        end: Number(match[2]),
        label: match[3].trim(),
      } satisfies FrameRange;
    })
    .filter((value): value is FrameRange => Boolean(value));

const chooseFrameRange = (ranges: FrameRange[]): FrameRange | null => {
  if (ranges.length === 0) {
    return null;
  }

  const latestRangeEnd = ranges[ranges.length - 1]?.end ?? 0;
  const holdRange = [...ranges]
    .reverse()
    .find(
      (range) =>
        HOLD_RE.test(range.label) &&
        range.start >= latestRangeEnd / 2
    );
  return holdRange ?? ranges[ranges.length - 1];
};

const midpointSample = (startSeconds: number, endSeconds: number): number =>
  Math.max(
    startSeconds,
    startSeconds + (endSeconds - startSeconds) / 2 - FRAME_SAMPLE_EPSILON_SECONDS,
  );

const toIntrinsicSampleFrame = (
  sampleSeconds: number,
  durationFrames: number,
  fps: number,
): number =>
  Math.min(
    Math.max(durationFrames - 1, 0),
    Math.max(0, Math.floor(sampleSeconds * fps))
  );

export function resolveAuditSampleWindow(
  specContent: string,
  options: ResolveOptions,
): AuditSampleWindow {
  const timestampWindow = parseTimestampWindow(specContent, options);
  const frameRanges = parseFrameRanges(specContent);
  const selectedRange = chooseFrameRange(frameRanges);

  if (timestampWindow && selectedRange) {
    const localFrameDuration = Math.max(...frameRanges.map((range) => range.end), selectedRange.end, 1);
    const rawWindowDuration = Math.max(timestampWindow.end - timestampWindow.start, 0);
    const startSeconds = timestampWindow.start + (selectedRange.start / localFrameDuration) * rawWindowDuration;
    const endSeconds = timestampWindow.start + (selectedRange.end / localFrameDuration) * rawWindowDuration;
    const clampedEnd = clampEndToSection(
      Math.min(endSeconds, timestampWindow.end),
      options.sectionDurationSeconds,
    );
    const clampedStart = Math.min(startSeconds, clampedEnd);
    const sampleSeconds = midpointSample(clampedStart, clampedEnd);
    const intrinsicDurationSeconds = Math.max(
      localFrameDuration / options.fps,
      FRAME_SAMPLE_EPSILON_SECONDS
    );
    const intrinsicSampleSeconds = midpointSample(
      selectedRange.start / options.fps,
      selectedRange.end / options.fps
    );
    const intrinsicDurationFrames = Math.max(localFrameDuration, 1);
    const normalizedSample = Math.min(
      1,
      Math.max(0, intrinsicSampleSeconds / intrinsicDurationSeconds)
    );

    return {
      source: "frame-range",
      startSeconds: clampedStart,
      endSeconds: clampedEnd,
      sampleSeconds,
      intrinsicDurationSeconds,
      intrinsicSampleSeconds,
      intrinsicDurationFrames,
      intrinsicSampleFrame: toIntrinsicSampleFrame(
        intrinsicSampleSeconds,
        intrinsicDurationFrames,
        options.fps
      ),
      normalizedSample,
    };
  }

  if (selectedRange) {
    const startSeconds = selectedRange.start / options.fps;
    const endSeconds = clampEndToSection(selectedRange.end / options.fps, options.sectionDurationSeconds);
    const sampleSeconds = midpointSample(startSeconds, endSeconds);
    const intrinsicDurationFrames = Math.max(
      ...frameRanges.map((range) => range.end),
      selectedRange.end,
      1
    );
    const intrinsicDurationSeconds = Math.max(
      intrinsicDurationFrames / options.fps,
      FRAME_SAMPLE_EPSILON_SECONDS
    );
    const normalizedSample = Math.min(
      1,
      Math.max(0, sampleSeconds / intrinsicDurationSeconds)
    );
    return {
      source: "frame-range",
      startSeconds,
      endSeconds,
      sampleSeconds,
      intrinsicDurationSeconds,
      intrinsicSampleSeconds: sampleSeconds,
      intrinsicDurationFrames,
      intrinsicSampleFrame: toIntrinsicSampleFrame(
        sampleSeconds,
        intrinsicDurationFrames,
        options.fps
      ),
      normalizedSample,
    };
  }

  if (timestampWindow) {
    const startSeconds = Math.min(timestampWindow.start, options.sectionDurationSeconds);
    const endSeconds = clampEndToSection(timestampWindow.end, options.sectionDurationSeconds);
    const intrinsicDurationSeconds = Math.max(
      timestampWindow.end - timestampWindow.start,
      FRAME_SAMPLE_EPSILON_SECONDS
    );
    const sampleSeconds = startSeconds + (endSeconds - startSeconds) * 0.75;
    const intrinsicSampleSeconds = Math.max(0, sampleSeconds - timestampWindow.start);
    const intrinsicDurationFrames = Math.max(
      1,
      Math.round(intrinsicDurationSeconds * options.fps)
    );
    const normalizedSample = Math.min(
      1,
      Math.max(0, intrinsicSampleSeconds / intrinsicDurationSeconds)
    );
    return {
      source: "timestamp",
      startSeconds,
      endSeconds,
      sampleSeconds,
      intrinsicDurationSeconds,
      intrinsicSampleSeconds,
      intrinsicDurationFrames,
      intrinsicSampleFrame: toIntrinsicSampleFrame(
        intrinsicSampleSeconds,
        intrinsicDurationFrames,
        options.fps
      ),
      normalizedSample,
    };
  }

  const midpoint = options.sectionDurationSeconds / 2;
  const intrinsicDurationSeconds = Math.max(
    options.sectionDurationSeconds,
    FRAME_SAMPLE_EPSILON_SECONDS
  );
  const intrinsicDurationFrames = Math.max(
    1,
    Math.round(intrinsicDurationSeconds * options.fps)
  );
  return {
    source: "fallback",
    startSeconds: midpoint,
    endSeconds: midpoint,
    sampleSeconds: midpoint,
    intrinsicDurationSeconds,
    intrinsicSampleSeconds: midpoint,
    intrinsicDurationFrames,
    intrinsicSampleFrame: toIntrinsicSampleFrame(
      midpoint,
      intrinsicDurationFrames,
      options.fps
    ),
    normalizedSample: 0.5,
  };
}

const resolveSpecDir = (projectDir: string, specDir: string): string =>
  path.isAbsolute(specDir)
    ? specDir
    : path.join(projectDir, "specs", specDir.replace(/^specs[\\/]/, ""));

const getRawTimelineDuration = (specDir: string): number => {
  if (!fs.existsSync(specDir)) {
    return 0;
  }

  let maxEnd = 0;
  for (const entry of fs.readdirSync(specDir)) {
    if (!entry.endsWith(".md") || entry.startsWith("AUDIT_")) {
      continue;
    }

    const content = fs.readFileSync(path.join(specDir, entry), "utf-8");
    const timestampWindow = parseTimestampWindow(content, {
      sectionDurationSeconds: Number.MAX_SAFE_INTEGER,
      fps: 30,
      sectionOffsetSeconds: 0,
    });
    if (timestampWindow) {
      maxEnd = Math.max(maxEnd, timestampWindow.end);
    }
  }

  return maxEnd;
};

const toConfiguredCompositionIds = (section: Section): string[] =>
  (section.compositions ?? [])
    .map((composition) =>
      typeof composition === "string" ? composition : composition?.id
    )
    .filter((compositionId): compositionId is string => Boolean(compositionId));

export function resolveRenderedAuditSampleWindow(
  specContent: string,
  options: RenderedResolveOptions,
): AuditSampleWindow {
  const sectionNarrativeTiming = resolveSectionNarrativeTiming(
    options.projectDir,
    options.section
  );
  const rawTimelineDuration = getRawTimelineDuration(
    resolveSpecDir(options.projectDir, options.section.specDir)
  );
  const rawSample = resolveAuditSampleWindow(specContent, {
    sectionDurationSeconds:
      sectionNarrativeTiming.durationSeconds > 0
        ? sectionNarrativeTiming.durationSeconds
        : rawTimelineDuration,
    fps: options.fps,
    sectionOffsetSeconds: sectionNarrativeTiming.offsetSeconds,
  });
  const configuredCompositionIds = toConfiguredCompositionIds(options.section);
  const matchedVisual = resolveSectionVisuals(
    options.projectDir,
    options.section,
    configuredCompositionIds
  ).find(
    (visual) =>
      visual.specPath &&
      path.resolve(visual.specPath) === path.resolve(options.specPath)
  );

  if (!matchedVisual) {
    return rawSample;
  }

  const renderedTiming = resolveSectionVisualTimings(
    options.projectDir,
    options.section,
    configuredCompositionIds
  ).find((timing) => timing.id === matchedVisual.id);

  if (!renderedTiming || renderedTiming.endSeconds <= renderedTiming.startSeconds) {
    return rawSample;
  }
  const slotStart = renderedTiming.startSeconds;
  const slotEnd = renderedTiming.endSeconds;
  const slotDuration = Math.max(
    slotEnd - slotStart,
    FRAME_SAMPLE_EPSILON_SECONDS
  );
  const guardBand = Math.min(2 / options.fps, slotDuration / 4);
  const guardedStart = Math.min(slotEnd, slotStart + guardBand);
  const guardedEnd = Math.max(guardedStart, slotEnd - guardBand);

  return {
    ...rawSample,
    startSeconds: slotStart,
    endSeconds: slotEnd,
    sampleSeconds:
      guardedStart + (guardedEnd - guardedStart) * rawSample.normalizedSample,
  };
}
