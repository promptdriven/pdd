import fs from "fs";
import path from "path";

import { getProjectDir } from "@/lib/projects";
import {
  loadVisualContractManifest,
  type GeneratedVisualContract,
  type GeneratedTimingAnchor,
} from "@/app/api/pipeline/_lib/visual-contract-manifest";
import {
  resolveSegmentTimingForSection,
  type NarrationSegment,
} from "./narration-manifest";
import { resolveSectionNarrativeTiming } from "./section-timing";
import { parseSpecTimestampRange } from "./composition-timing";
import type { Section } from "./types";

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type TimelineEntrySource =
  | "segment-anchor"
  | "absolute"
  | "timestamp-fallback"
  | "audio-sync"
  | "fallback";

export type TimelineAnchor = GeneratedTimingAnchor;

export type TimelineEntry = {
  id: string;
  start?: TimelineAnchor;
  end?: TimelineAnchor;
  resolvedStartSeconds?: number;
  resolvedEndSeconds?: number;
  startSeconds: number;
  endSeconds: number;
  lane: number;
  source: TimelineEntrySource;
  desc: string;
  coverSegments?: string[];
};

export type SectionTimeline = {
  sectionId: string;
  durationSeconds: number;
  entries: TimelineEntry[];
};

export type SectionTimelineManifest = {
  version: 1;
  updatedAt: string;
  sections: SectionTimeline[];
};

// ---------------------------------------------------------------------------
// File paths
// ---------------------------------------------------------------------------

export function getSectionTimelineManifestPath(
  projectDir = getProjectDir()
): string {
  return path.join(
    projectDir,
    "outputs",
    "compositions",
    "section-timeline.json"
  );
}

// ---------------------------------------------------------------------------
// Loader
// ---------------------------------------------------------------------------

function normalizeTimelineEntry(
  entry: unknown,
  sectionDuration: number
): TimelineEntry | null {
  if (!entry || typeof entry !== "object") {
    return null;
  }

  const raw = entry as Partial<TimelineEntry>;
  if (
    typeof raw.id !== "string" ||
    typeof raw.lane !== "number" ||
    typeof raw.source !== "string" ||
    typeof raw.desc !== "string"
  ) {
    return null;
  }

  const start = raw.start ?? (
    typeof raw.startSeconds === "number"
      ? { type: "absolute", seconds: raw.startSeconds } satisfies TimelineAnchor
      : undefined
  );
  const end = raw.end ?? (
    typeof raw.endSeconds === "number"
      ? { type: "absolute", seconds: raw.endSeconds } satisfies TimelineAnchor
      : undefined
  );

  const resolvedStartSeconds =
    raw.resolvedStartSeconds ??
    raw.startSeconds ??
    (start?.type === "absolute"
      ? start.seconds
      : start?.type === "sectionStart"
        ? (start.offsetMs ?? 0) / 1000
        : start?.type === "sectionEnd"
          ? sectionDuration + (start.offsetMs ?? 0) / 1000
          : null);
  const resolvedEndSeconds =
    raw.resolvedEndSeconds ??
    raw.endSeconds ??
    (end?.type === "absolute"
      ? end.seconds
      : end?.type === "sectionStart"
        ? (end.offsetMs ?? 0) / 1000
        : end?.type === "sectionEnd"
          ? sectionDuration + (end.offsetMs ?? 0) / 1000
          : null);

  if (!start || !end || resolvedStartSeconds === null || resolvedEndSeconds === null) {
    return null;
  }

  return {
    id: raw.id,
    start,
    end,
    resolvedStartSeconds,
    resolvedEndSeconds,
    startSeconds: resolvedStartSeconds,
    endSeconds: resolvedEndSeconds,
    lane: raw.lane,
    source: raw.source as TimelineEntrySource,
    desc: raw.desc,
    coverSegments: raw.coverSegments,
  };
}

export function loadSectionTimeline(
  projectDir = getProjectDir()
): SectionTimelineManifest | null {
  const manifestPath = getSectionTimelineManifestPath(projectDir);
  if (!fs.existsSync(manifestPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
    if (
      !parsed ||
      parsed.version !== 1 ||
      !Array.isArray(parsed.sections) ||
      typeof parsed.updatedAt !== "string"
    ) {
      return null;
    }

    const sections = parsed.sections
      .map((section: Partial<SectionTimeline>) => {
        if (
          typeof section?.sectionId !== "string" ||
          typeof section?.durationSeconds !== "number" ||
          !Array.isArray(section?.entries)
        ) {
          return null;
        }

        return {
          sectionId: section.sectionId,
          durationSeconds: section.durationSeconds,
          entries: section.entries
            .map((entry) => normalizeTimelineEntry(entry, section.durationSeconds!))
            .filter((entry): entry is TimelineEntry => entry !== null),
        } satisfies SectionTimeline;
      })
      .filter((section): section is SectionTimeline => section !== null);

    return {
      version: 1,
      updatedAt: parsed.updatedAt,
      sections,
    };
  } catch {
    return null;
  }
}

export function resolveSectionTimelineEntries(
  sectionId: string,
  projectDir = getProjectDir()
): TimelineEntry[] {
  const manifest = loadSectionTimeline(projectDir);
  if (!manifest) {
    return [];
  }

  const section = manifest.sections.find((candidate) => candidate.sectionId === sectionId);
  return section?.entries ?? [];
}

// ---------------------------------------------------------------------------
// Lane mapping
// ---------------------------------------------------------------------------

function laneHintToNumber(hint: GeneratedVisualContract["laneHint"]): number {
  if (typeof hint === "number" && Number.isFinite(hint)) return hint;
  if (hint === "overlay") return 1;
  if (hint === "background") return -1;
  return 0;
}

function resolveAnchorSeconds(
  anchor: TimelineAnchor,
  segmentById: Map<string, NarrationSegment>,
  sectionDuration: number
): number | null {
  const offsetSeconds = (anchor.offsetMs ?? 0) / 1000;

  if (anchor.type === "absolute") {
    return anchor.seconds;
  }

  if (anchor.type === "sectionStart") {
    return 0 + offsetSeconds;
  }

  if (anchor.type === "sectionEnd") {
    return sectionDuration + offsetSeconds;
  }

  const segment = segmentById.get(anchor.segmentId);
  if (!segment) {
    return null;
  }

  const baseSeconds =
    anchor.type === "segmentStart" ? segment.startSeconds : segment.endSeconds;
  if (typeof baseSeconds !== "number") {
    return null;
  }

  return baseSeconds + offsetSeconds;
}

function buildTimelineEntry(
  params: {
    id: string;
    start: TimelineAnchor;
    end: TimelineAnchor;
    lane: number;
    source: TimelineEntrySource;
    desc: string;
    coverSegments?: string[];
  },
  resolvedStartSeconds: number,
  resolvedEndSeconds: number
): TimelineEntry {
  return {
    id: params.id,
    start: params.start,
    end: params.end,
    resolvedStartSeconds,
    resolvedEndSeconds,
    startSeconds: resolvedStartSeconds,
    endSeconds: resolvedEndSeconds,
    lane: params.lane,
    source: params.source,
    desc: params.desc,
    coverSegments: params.coverSegments,
  };
}

// ---------------------------------------------------------------------------
// Holistic timeline resolver
// ---------------------------------------------------------------------------

type SectionTimingTarget = Pick<
  Section,
  "id" | "specDir" | "durationSeconds" | "compositionId"
> & {
  label?: Section["label"];
  offsetSeconds?: Section["offsetSeconds"];
  compositions?: Section["compositions"];
};

export function buildSectionTimeline(
  projectDir: string,
  section: SectionTimingTarget
): SectionTimeline {
  const sectionId = section.id;
  const narrativeTiming = resolveSectionNarrativeTiming(projectDir, section);
  const segments = resolveSegmentTimingForSection(sectionId, projectDir);

  const visualManifest = loadVisualContractManifest(projectDir);
  const sectionVisuals =
    visualManifest?.sections.find((candidate) => candidate.id === sectionId)?.visuals ?? [];

  const childIds = new Set<string>();
  for (const visual of sectionVisuals) {
    for (const childId of visual.children ?? []) {
      childIds.add(childId);
    }
  }

  const segmentById = new Map<string, NarrationSegment>();
  for (const segment of segments) {
    segmentById.set(segment.id, segment);
  }

  const entries: TimelineEntry[] = [];
  let sectionDuration = narrativeTiming.durationSeconds;

  for (const visual of sectionVisuals) {
    if (childIds.has(visual.id) || visual.parentId) {
      continue;
    }

    const lane = laneHintToNumber(visual.laneHint);
    const desc = visual.specBaseName.replace(/_/g, " ");
    const startOffsetMs =
      typeof visual.startOffsetMs === "number" ? visual.startOffsetMs : 0;
    const endOffsetMs =
      typeof visual.endOffsetMs === "number" ? visual.endOffsetMs : 0;

    const pushResolvedEntry = (
      start: TimelineAnchor,
      end: TimelineAnchor,
      source: TimelineEntrySource
    ): boolean => {
      const resolvedStart = resolveAnchorSeconds(start, segmentById, sectionDuration);
      const resolvedEnd = resolveAnchorSeconds(end, segmentById, sectionDuration);
      if (resolvedStart === null || resolvedEnd === null) {
        return false;
      }

      entries.push(
        buildTimelineEntry(
          {
            id: visual.id,
            start,
            end,
            lane,
            source,
            desc,
            coverSegments: visual.coverSegments,
          },
          resolvedStart,
          resolvedEnd
        )
      );
      return true;
    };

    if (visual.startAnchor && visual.endAnchor) {
      const source =
        visual.startAnchor.type === "absolute" ||
        visual.endAnchor.type === "absolute" ||
        visual.startAnchor.type.startsWith("section") ||
        visual.endAnchor.type.startsWith("section")
          ? "absolute"
          : "segment-anchor";
      if (pushResolvedEntry(visual.startAnchor, visual.endAnchor, source)) {
        continue;
      }
    }

    if (visual.coverSegments && visual.coverSegments.length > 0) {
      const firstSegmentId = visual.coverSegments[0];
      const lastSegmentId = visual.coverSegments[visual.coverSegments.length - 1];
      if (firstSegmentId && lastSegmentId) {
        const startAnchor =
          visual.startAnchor ??
          ({
            type: "segmentStart",
            segmentId: firstSegmentId,
            ...(startOffsetMs !== 0 ? { offsetMs: startOffsetMs } : {}),
          } satisfies TimelineAnchor);
        const endAnchor =
          visual.endAnchor ??
          ({
            type: "segmentEnd",
            segmentId: lastSegmentId,
            ...(endOffsetMs !== 0 ? { offsetMs: endOffsetMs } : {}),
          } satisfies TimelineAnchor);
        const source =
          startAnchor.type === "absolute" ||
          endAnchor.type === "absolute" ||
          startAnchor.type.startsWith("section") ||
          endAnchor.type.startsWith("section")
            ? "absolute"
            : "segment-anchor";
        if (pushResolvedEntry(startAnchor, endAnchor, source)) {
          continue;
        }
      }
    }

    if (visual.specPath) {
      const specFullPath = path.join(projectDir, visual.specPath);
      if (fs.existsSync(specFullPath)) {
        try {
          const specContent = fs.readFileSync(specFullPath, "utf-8");
          const range = parseSpecTimestampRange(specContent);
          if (range) {
            const specDuration = range.endSeconds;
            const scale =
              specDuration > 0 && sectionDuration > 0
                ? sectionDuration / specDuration
                : 1;
            const startSeconds = range.startSeconds * scale;
            const endSeconds = Math.min(range.endSeconds * scale, sectionDuration);
            entries.push(
              buildTimelineEntry(
                {
                  id: visual.id,
                  start: { type: "absolute", seconds: startSeconds },
                  end: { type: "absolute", seconds: endSeconds },
                  lane,
                  source: "timestamp-fallback",
                  desc,
                },
                startSeconds,
                endSeconds
              )
            );
            continue;
          }
        } catch {
          // fall through to generic fallback
        }
      }
    }

    entries.push(
      buildTimelineEntry(
        {
          id: visual.id,
          start: { type: "absolute", seconds: 0 },
          end: { type: "absolute", seconds: 0 },
          lane,
          source: "fallback",
          desc,
        },
        0,
        0
      )
    );
  }

  const fallbackEntries = entries.filter((entry) => entry.source === "fallback");
  if (fallbackEntries.length > 0) {
    const timedEntries = entries.filter((entry) => entry.source !== "fallback");
    const timedEnd =
      timedEntries.length > 0
        ? Math.max(...timedEntries.map((entry) => entry.resolvedEndSeconds ?? entry.endSeconds))
        : 0;
    const availableStart = timedEnd;
    const availableDuration = Math.max(sectionDuration - availableStart, 0);
    const sliceDuration =
      fallbackEntries.length > 0 ? availableDuration / fallbackEntries.length : 0;

    fallbackEntries.forEach((entry, index) => {
      const startSeconds = availableStart + index * sliceDuration;
      const endSeconds = availableStart + (index + 1) * sliceDuration;
      entry.start = { type: "absolute", seconds: startSeconds };
      entry.end = { type: "absolute", seconds: endSeconds };
      entry.resolvedStartSeconds = startSeconds;
      entry.resolvedEndSeconds = endSeconds;
      entry.startSeconds = startSeconds;
      entry.endSeconds = endSeconds;
    });
  }

  entries.sort((left, right) => {
    const leftStart = left.resolvedStartSeconds ?? left.startSeconds;
    const rightStart = right.resolvedStartSeconds ?? right.startSeconds;
    if (leftStart !== rightStart) {
      return leftStart - rightStart;
    }
    if (left.lane !== right.lane) {
      return left.lane - right.lane;
    }
    return left.id.localeCompare(right.id);
  });

  const maxEntryEnd =
    entries.length > 0
      ? Math.max(...entries.map((entry) => entry.resolvedEndSeconds ?? entry.endSeconds))
      : 0;
  sectionDuration = Math.max(sectionDuration, maxEntryEnd);

  return {
    sectionId,
    durationSeconds: sectionDuration,
    entries,
  };
}

// ---------------------------------------------------------------------------
// Writer / merger
// ---------------------------------------------------------------------------

export function writeSectionTimelineManifest(
  sectionTimelines: SectionTimeline[],
  projectDir = getProjectDir()
): void {
  const existing = loadSectionTimeline(projectDir);
  const mergedById = new Map<string, SectionTimeline>();

  for (const section of existing?.sections ?? []) {
    mergedById.set(section.sectionId, section);
  }

  for (const section of sectionTimelines) {
    mergedById.set(section.sectionId, section);
  }

  const manifest: SectionTimelineManifest = {
    version: 1,
    updatedAt: new Date().toISOString(),
    sections: Array.from(mergedById.values()),
  };

  const manifestPath = getSectionTimelineManifestPath(projectDir);
  fs.mkdirSync(path.dirname(manifestPath), { recursive: true });
  fs.writeFileSync(manifestPath, JSON.stringify(manifest, null, 2), "utf-8");
}
