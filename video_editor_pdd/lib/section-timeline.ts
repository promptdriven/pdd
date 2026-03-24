import fs from "fs";
import path from "path";

import { getProjectDir } from "@/lib/projects";
import {
  loadVisualContractManifest,
  type GeneratedVisualContract,
} from "@/app/api/pipeline/_lib/visual-contract-manifest";
import {
  resolveSegmentTimingForSection,
  type NarrationSegment,
} from "./narration-manifest";
import { resolveSectionNarrativeTiming } from "./section-timing";
import {
  parseSpecTimestampRange,
  type ResolvedVisualTiming,
  type TimingSource,
} from "./composition-timing";
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

export type TimelineEntry = {
  id: string;
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
    return parsed as SectionTimelineManifest;
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

  const section = manifest.sections.find((s) => s.sectionId === sectionId);
  return section?.entries ?? [];
}

// ---------------------------------------------------------------------------
// Lane mapping
// ---------------------------------------------------------------------------

function laneHintToNumber(
  hint: GeneratedVisualContract["laneHint"]
): number {
  if (hint === "overlay") return 1;
  if (hint === "background") return -1;
  return 0; // "main" or undefined
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
    visualManifest?.sections.find((s) => s.id === sectionId)?.visuals ?? [];

  // Build a set of child visual IDs to exclude from timeline entries
  const childIds = new Set<string>();
  for (const visual of sectionVisuals) {
    if (visual.children) {
      for (const childId of visual.children) {
        childIds.add(childId);
      }
    }
  }

  // Build a segment lookup by ID for fast access
  const segmentById = new Map<string, NarrationSegment>();
  for (const seg of segments) {
    segmentById.set(seg.id, seg);
  }

  const entries: TimelineEntry[] = [];

  for (const visual of sectionVisuals) {
    // Exclude children from top-level entries
    if (childIds.has(visual.id)) {
      continue;
    }

    const lane = laneHintToNumber(visual.laneHint);
    const desc = visual.specBaseName.replace(/_/g, " ");

    // Strategy 1: Use coverSegments to derive timing from narration manifest
    if (visual.coverSegments && visual.coverSegments.length > 0) {
      const coveredSegments = visual.coverSegments
        .map((segId) => segmentById.get(segId))
        .filter(
          (seg): seg is NarrationSegment =>
            seg !== undefined &&
            typeof seg.startSeconds === "number" &&
            typeof seg.endSeconds === "number"
        );

      if (coveredSegments.length > 0) {
        const startSeconds = Math.min(
          ...coveredSegments.map((s) => s.startSeconds!)
        );
        const endSeconds = Math.max(
          ...coveredSegments.map((s) => s.endSeconds!)
        );

        entries.push({
          id: visual.id,
          startSeconds,
          endSeconds,
          lane,
          source: "segment-anchor",
          desc,
          coverSegments: visual.coverSegments,
        });
        continue;
      }
    }

    // Strategy 2: Fall back to spec **Timestamp:** parsing
    if (visual.specPath) {
      const specFullPath = path.join(projectDir, visual.specPath);
      if (fs.existsSync(specFullPath)) {
        try {
          const specContent = fs.readFileSync(specFullPath, "utf-8");
          const range = parseSpecTimestampRange(specContent);
          if (range) {
            // Scale spec timestamps to section duration (same as existing logic)
            const specDuration = range.endSeconds;
            const sectionDuration = narrativeTiming.durationSeconds;
            const scale =
              specDuration > 0 && sectionDuration > 0
                ? sectionDuration / specDuration
                : 1;
            const startSeconds = range.startSeconds * scale;
            const endSeconds = range.endSeconds * scale;

            entries.push({
              id: visual.id,
              startSeconds,
              endSeconds: Math.min(endSeconds, sectionDuration),
              lane,
              source: "timestamp-fallback",
              desc,
            });
            continue;
          }
        } catch {
          // Fall through
        }
      }
    }

    // Strategy 3: Fallback — distribute evenly
    entries.push({
      id: visual.id,
      startSeconds: 0,
      endSeconds: 0, // Will be filled by distribution pass
      lane,
      source: "fallback",
      desc,
    });
  }

  // Distribute untimed (fallback) entries across gaps
  const sectionDuration = narrativeTiming.durationSeconds;
  const fallbackEntries = entries.filter((e) => e.source === "fallback");
  if (fallbackEntries.length > 0) {
    const timedEntries = entries.filter((e) => e.source !== "fallback");
    const timedEnd = timedEntries.length > 0
      ? Math.max(...timedEntries.map((e) => e.endSeconds))
      : 0;
    const availableStart = timedEnd;
    const availableDuration = Math.max(sectionDuration - availableStart, 0);
    const sliceDuration =
      fallbackEntries.length > 0
        ? availableDuration / fallbackEntries.length
        : 0;

    fallbackEntries.forEach((entry, index) => {
      entry.startSeconds = availableStart + index * sliceDuration;
      entry.endSeconds = availableStart + (index + 1) * sliceDuration;
    });
  }

  // Sequentialize same-lane overlaps (lane 0 only by default)
  const laneGroups = new Map<number, TimelineEntry[]>();
  for (const entry of entries) {
    const group = laneGroups.get(entry.lane) ?? [];
    group.push(entry);
    laneGroups.set(entry.lane, group);
  }

  for (const [, group] of laneGroups) {
    group.sort((a, b) => a.startSeconds - b.startSeconds);
    for (let i = 1; i < group.length; i++) {
      const prev = group[i - 1];
      const curr = group[i];
      if (curr.startSeconds < prev.endSeconds) {
        curr.startSeconds = prev.endSeconds;
        if (curr.endSeconds < curr.startSeconds) {
          curr.endSeconds = curr.startSeconds;
        }
      }
    }
  }

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
