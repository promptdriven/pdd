import type { ProjectConfig, Section } from "@/lib/types";

type SegmentRange = {
  startSegment: string;
  endSegment: string;
};

type DetectableSegment = {
  id: string;
};

export function expandSegmentRange(start: string, end: string): string[] {
  const sm = start.match(/^(.+)_(\d{3})$/);
  const em = end.match(/^(.+)_(\d{3})$/);
  if (!sm || !em || sm[1] !== em[1]) {
    return [start, end].filter(Boolean);
  }

  const prefix = sm[1];
  const s = parseInt(sm[2], 10);
  const e = parseInt(em[2], 10);
  const result: string[] = [];
  for (let i = s; i <= e; i += 1) {
    result.push(`${prefix}_${String(i).padStart(3, "0")}`);
  }
  return result;
}

export function normalizeAudioSyncSectionGroups(
  rawGroups: unknown
): Record<string, string[]> {
  const normalized: Record<string, string[]> = {};
  if (!rawGroups || typeof rawGroups !== "object") {
    return normalized;
  }

  for (const [key, value] of Object.entries(rawGroups)) {
    if (Array.isArray(value)) {
      normalized[key] = value.filter(
        (segmentId): segmentId is string => typeof segmentId === "string"
      );
      continue;
    }

    if (
      value &&
      typeof value === "object" &&
      "startSegment" in value &&
      "endSegment" in value
    ) {
      const range = value as SegmentRange;
      normalized[key] = expandSegmentRange(
        range.startSegment,
        range.endSegment
      );
      continue;
    }

    normalized[key] = [];
  }

  return normalized;
}

function inferSectionGroupsFromSegments(
  sections: Section[],
  segments: DetectableSegment[]
): {
  grouped: Record<string, string[]>;
  unmatchedSegments: string[];
} {
  const sectionIds = sections.map((section) => section.id);
  const sortedSectionIds = [...sectionIds].sort((a, b) => b.length - a.length);

  const grouped: Record<string, string[]> = {};
  const unmatchedSegments: string[] = [];

  for (const segment of segments) {
    let matched = false;
    let prefixMatched = false;

    for (const sectionId of sortedSectionIds) {
      const prefix = `${sectionId}_`;
      if (!segment.id.startsWith(prefix)) {
        continue;
      }

      prefixMatched = true;
      const suffix = segment.id.slice(prefix.length);
      if (/^\d{3}$/.test(suffix)) {
        if (!grouped[sectionId]) {
          grouped[sectionId] = [];
        }
        grouped[sectionId].push(segment.id);
        matched = true;
        break;
      }
    }

    if (!matched && prefixMatched) {
      unmatchedSegments.push(segment.id);
    }
  }

  return { grouped, unmatchedSegments };
}

export function fillMissingAudioSyncSectionGroups(options: {
  sections: Section[];
  existingGroups: Record<string, string[]>;
  segments: DetectableSegment[];
}): {
  groups: Record<string, string[]>;
  filledSections: string[];
  unmatchedSegments: string[];
  changed: boolean;
} {
  const { sections, existingGroups, segments } = options;
  const { grouped, unmatchedSegments } = inferSectionGroupsFromSegments(
    sections,
    segments
  );

  const nextGroups: Record<string, string[]> = { ...existingGroups };
  const filledSections: string[] = [];

  for (const [sectionId, segmentIds] of Object.entries(grouped)) {
    const existing = existingGroups[sectionId] ?? [];
    if (existing.length > 0) {
      continue;
    }

    nextGroups[sectionId] = [...segmentIds].sort();
    filledSections.push(sectionId);
  }

  return {
    groups: nextGroups,
    filledSections,
    unmatchedSegments,
    changed: filledSections.length > 0,
  };
}

export function toSegmentRangeSectionGroups(
  sectionGroups: Record<string, string[]>
): Record<string, SegmentRange> {
  const rangeGroups: Record<string, SegmentRange> = {};
  for (const [sectionId, segments] of Object.entries(sectionGroups)) {
    if (segments.length === 0) {
      continue;
    }

    rangeGroups[sectionId] = {
      startSegment: segments[0],
      endSegment: segments[segments.length - 1],
    };
  }

  return rangeGroups;
}

export async function prepareAudioSyncAutomation(
  fetchImpl: typeof fetch
): Promise<{
  changed: boolean;
  filledSections: string[];
  unmatchedSegments: string[];
}> {
  const projectResponse = await fetchImpl("/api/project");
  if (!projectResponse.ok) {
    throw new Error("Failed to load project before running audio sync");
  }

  const project = (await projectResponse.json()) as ProjectConfig;
  const sections = project.sections ?? [];
  const existingGroups = normalizeAudioSyncSectionGroups(
    project.audioSync?.sectionGroups ?? {}
  );

  const missingSectionIds = sections
    .map((section) => section.id)
    .filter((sectionId) => (existingGroups[sectionId] ?? []).length === 0);

  if (missingSectionIds.length === 0) {
    return { changed: false, filledSections: [], unmatchedSegments: [] };
  }

  const segmentsResponse = await fetchImpl("/api/pipeline/tts-render/segments");
  if (!segmentsResponse.ok) {
    throw new Error("Failed to detect Stage 5 section groups from TTS segments");
  }

  const rawSegments = await segmentsResponse.json();
  const segments = Array.isArray(rawSegments)
    ? rawSegments
    : Array.isArray(rawSegments?.segments)
      ? rawSegments.segments
      : [];

  const { groups, filledSections, unmatchedSegments, changed } =
    fillMissingAudioSyncSectionGroups({
      sections,
      existingGroups,
      segments,
    });

  if (!changed) {
    return { changed: false, filledSections: [], unmatchedSegments };
  }

  const saveResponse = await fetchImpl("/api/project", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({
      audioSync: {
        ...project.audioSync,
        sectionGroups: toSegmentRangeSectionGroups(groups),
      },
    }),
  });

  if (!saveResponse.ok) {
    throw new Error("Failed to save auto-detected audio sync section groups");
  }

  return {
    changed: true,
    filledSections,
    unmatchedSegments,
  };
}
