import fs from "fs";
import path from "path";

import { getProjectDir } from "@/lib/projects";
import { loadLatestWordTimestamps } from "@/lib/audio-sync-artifacts";

export type NarrationSegment = {
  id: string;
  sectionId: string;
  startSeconds?: number;
  endSeconds?: number;
  text: string;
  cleanText: string;
};

type NarrationManifest = {
  segments: NarrationSegment[];
};

type WordTimestamp = {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
};

export type NarrativeHeadingLike = {
  heading: string;
  [key: string]: unknown;
};

export type SectionHeadingOwner = {
  id: string;
  label: string;
  scriptHeadings?: string[];
};

export type NarrativeHeadingAssignmentSource =
  | "exact"
  | "fuzzy"
  | "explicit"
  | "fold_previous"
  | "fold_next"
  | "unmatched";

export type AssignedNarrativeHeading<T extends NarrativeHeadingLike> = T & {
  normalizedHeading: string;
  pipelineSectionId: string | null;
  pipelineSectionLabel: string | null;
  matchSource: NarrativeHeadingAssignmentSource;
};

export type NarrativeStructureEntry = {
  headingId: string;
  order: number;
  heading: string;
  normalizedHeading: string;
  narration: string[];
  pipelineSectionId: string | null;
  pipelineSectionLabel: string | null;
  matchSource: NarrativeHeadingAssignmentSource;
  kind: "section" | "folded_heading" | "unmatched";
};

export type NarrativeStructureManifest = {
  headings: NarrativeStructureEntry[];
};

/**
 * Load the enriched segments.json narration manifest from `outputs/tts/segments.json`.
 * Returns null when the manifest does not exist or cannot be parsed.
 */
export function loadNarrationManifest(
  projectDir = getProjectDir()
): NarrationManifest | null {
  const manifestPath = path.join(projectDir, "outputs", "tts", "segments.json");
  if (!fs.existsSync(manifestPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
    if (!parsed || !Array.isArray(parsed.segments)) {
      return null;
    }
    return parsed as NarrationManifest;
  } catch {
    return null;
  }
}

/**
 * Return narration segments for a specific section, enriched with timing.
 *
 * When segments already have `startSeconds`/`endSeconds` (from the enriched
 * manifest), those values are used directly. Otherwise falls back to loading
 * `word_timestamps.json` for the section and deriving timing from word boundaries.
 */
export function resolveSegmentTimingForSection(
  sectionId: string,
  projectDir = getProjectDir()
): NarrationSegment[] {
  const manifest = loadNarrationManifest(projectDir);
  if (!manifest) {
    return [];
  }

  const sectionSegments = manifest.segments.filter(
    (seg) => seg.sectionId === sectionId
  );

  // If all segments already have timing, return as-is
  const allTimed = sectionSegments.every(
    (seg) =>
      typeof seg.startSeconds === "number" &&
      typeof seg.endSeconds === "number"
  );
  if (allTimed) {
    return sectionSegments;
  }

  // Fall back: load word_timestamps.json and derive boundaries
  const words = loadWordTimestamps(projectDir, sectionId);
  if (!words || words.length === 0) {
    return sectionSegments;
  }

  return sectionSegments.map((seg) => {
    if (
      typeof seg.startSeconds === "number" &&
      typeof seg.endSeconds === "number"
    ) {
      return seg;
    }

    const matching = words.filter((w) => w.segmentId === seg.id);
    if (matching.length === 0) {
      return seg;
    }

    return {
      ...seg,
      startSeconds: Math.min(...matching.map((w) => w.start)),
      endSeconds: Math.max(...matching.map((w) => w.end)),
    };
  });
}

function loadWordTimestamps(
  projectDir: string,
  sectionId: string
): WordTimestamp[] | null {
  const words = loadLatestWordTimestamps(projectDir, sectionId);
  if (words.length === 0) {
    return null;
  }
  return words;
}

function collapseWhitespace(value: string): string {
  return value.replace(/\s+/g, " ").trim();
}

function headingSlug(value: string): string {
  return normalizeNarrativeHeading(value)
    .replace(/\s+/g, "_")
    .replace(/^_+|_+$/g, "");
}

function isTimedNarrativeHeading(value: string): boolean {
  return /\(\s*\d{1,2}:\d{2}\s*-\s*\d{1,2}:\d{2}\s*\)\s*$/i.test(value.trim());
}

function narrativeStructureManifestPath(projectDir = getProjectDir()): string {
  return path.join(projectDir, "outputs", "narrative", "structure.json");
}

export function normalizeNarrativeHeading(value: string): string {
  return collapseWhitespace(
    value
      .replace(/\([^)]*\)/g, " ")
      .replace(/([A-Za-z])(\d)/g, "$1 $2")
      .replace(/(\d)([A-Za-z])/g, "$1 $2")
      .replace(/[_-]+/g, " ")
      .replace(/[^A-Za-z0-9\s]/g, " ")
      .toLowerCase(),
  );
}

function titleFromId(sectionId: string): string {
  return sectionId
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0]?.toUpperCase() + part.slice(1))
    .join(" ");
}

function tokenOverlapScore(left: string, right: string): number {
  const leftTokens = left.split(" ").filter(Boolean);
  const rightTokens = right.split(" ").filter(Boolean);

  if (leftTokens.length === 0 || rightTokens.length === 0) {
    return 0;
  }

  const rightSet = new Set(rightTokens);
  const overlap = leftTokens.filter((token) => rightSet.has(token)).length;
  return overlap / Math.max(leftTokens.length, rightTokens.length);
}

const HEADING_STOPWORDS = new Set(["the", "a", "an"]);

function normalizeHeadingTokens(value: string): string[] {
  return normalizeNarrativeHeading(value)
    .split(" ")
    .filter(Boolean)
    .filter((token) => !HEADING_STOPWORDS.has(token));
}

function buildSectionHeadingCandidates(
  section: Pick<SectionHeadingOwner, "id" | "label">,
): string[] {
  return Array.from(
    new Set(
      [section.label, section.id, titleFromId(section.id)]
        .map(normalizeNarrativeHeading)
        .filter(Boolean),
    ),
  );
}

function resolveExplicitOwner(
  heading: string,
  projectSections: ReadonlyArray<SectionHeadingOwner>,
): Pick<AssignedNarrativeHeading<NarrativeHeadingLike>, "pipelineSectionId" | "pipelineSectionLabel" | "matchSource"> | null {
  const normalizedHeading = normalizeNarrativeHeading(heading);

  for (const section of projectSections) {
    const explicitHeadings = Array.isArray(section.scriptHeadings)
      ? section.scriptHeadings
      : [];
    if (
      explicitHeadings.some(
        (candidate) => normalizeNarrativeHeading(candidate) === normalizedHeading,
      )
    ) {
      return {
        pipelineSectionId: section.id,
        pipelineSectionLabel: section.label,
        matchSource: "explicit",
      };
    }
  }

  return null;
}

function scoreHeadingAgainstSection(
  heading: string,
  section: Pick<SectionHeadingOwner, "id" | "label">,
): number {
  const normalizedHeading = normalizeNarrativeHeading(heading);
  const headingTokens = normalizeHeadingTokens(heading);
  const candidates = buildSectionHeadingCandidates(section);
  let bestScore = 0;

  candidates.forEach((candidate) => {
    const condensedHeading = normalizedHeading.replace(/\s+/g, "");
    const condensedCandidate = candidate.replace(/\s+/g, "");
    const candidateTokens = normalizeHeadingTokens(candidate);

    if (normalizedHeading === candidate) {
      bestScore = Math.max(bestScore, 100);
      return;
    }

    if (condensedHeading === condensedCandidate) {
      bestScore = Math.max(bestScore, 95);
      return;
    }

    if (
      normalizedHeading.startsWith(candidate) ||
      candidate.startsWith(normalizedHeading)
    ) {
      bestScore = Math.max(bestScore, 90);
      return;
    }

    if (
      normalizedHeading.includes(candidate) ||
      candidate.includes(normalizedHeading)
    ) {
      bestScore = Math.max(bestScore, 80);
      return;
    }

    if (
      candidateTokens.length > 0 &&
      candidateTokens.every((token) => headingTokens.includes(token))
    ) {
      bestScore = Math.max(bestScore, 78);
      return;
    }

    if (
      headingTokens.length > 0 &&
      headingTokens.every((token) => candidateTokens.includes(token))
    ) {
      bestScore = Math.max(bestScore, 78);
      return;
    }

    bestScore = Math.max(
      bestScore,
      Math.round(tokenOverlapScore(normalizedHeading, candidate) * 70),
    );
  });

  return bestScore;
}

export function resolveNarrativeSectionAssignments<
  T extends NarrativeHeadingLike,
>(
  headings: ReadonlyArray<T>,
  projectSections: ReadonlyArray<SectionHeadingOwner>,
): Array<AssignedNarrativeHeading<T>> {
  const baseAssignments = headings.map((heading) => {
    const explicitOwner = resolveExplicitOwner(heading.heading, projectSections);
    if (explicitOwner) {
      return {
        ...heading,
        normalizedHeading: normalizeNarrativeHeading(heading.heading),
        ...explicitOwner,
      };
    }

    let bestSection: SectionHeadingOwner | null = null;
    let bestScore = 0;

    projectSections.forEach((section) => {
      const score = scoreHeadingAgainstSection(heading.heading, section);
      if (score > bestScore) {
        bestScore = score;
        bestSection = section;
      }
    });

    if (bestSection && bestScore >= 60) {
      return {
        ...heading,
        normalizedHeading: normalizeNarrativeHeading(heading.heading),
        pipelineSectionId: bestSection.id,
        pipelineSectionLabel: bestSection.label,
        matchSource: bestScore >= 95 ? "exact" : "fuzzy",
      };
    }

    return {
      ...heading,
      normalizedHeading: normalizeNarrativeHeading(heading.heading),
      pipelineSectionId: null,
      pipelineSectionLabel: null,
      matchSource: "unmatched" as const,
    };
  });

  return baseAssignments.map((assignment, index) => {
    if (assignment.pipelineSectionId) {
      return assignment;
    }

    const previous = [...baseAssignments]
      .slice(0, index)
      .reverse()
      .find((candidate) => candidate.pipelineSectionId);
    if (previous?.pipelineSectionId) {
      return {
        ...assignment,
        pipelineSectionId: previous.pipelineSectionId,
        pipelineSectionLabel: previous.pipelineSectionLabel,
        matchSource: "fold_previous" as const,
      };
    }

    const next = baseAssignments
      .slice(index + 1)
      .find((candidate) => candidate.pipelineSectionId);
    if (next?.pipelineSectionId) {
      return {
        ...assignment,
        pipelineSectionId: next.pipelineSectionId,
        pipelineSectionLabel: next.pipelineSectionLabel,
        matchSource: "fold_next" as const,
      };
    }

    return assignment;
  });
}

function extractNarrationParagraphs(body: string): string[] {
  const paragraphs: string[] = [];
  let currentLines: string[] = [];
  let narratorStarted = false;

  const flush = () => {
    const paragraph = collapseWhitespace(currentLines.join(" "));
    if (paragraph) {
      paragraphs.push(paragraph);
    }
    currentLines = [];
  };

  for (const line of body.split(/\r?\n/)) {
    const trimmed = line.trim();

    if (/^\*{0,2}NARRATOR:\*{0,2}\s*$/i.test(trimmed)) {
      flush();
      narratorStarted = true;
      continue;
    }

    if (!narratorStarted) {
      continue;
    }

    if (!trimmed) {
      flush();
      continue;
    }

    if (/^##\s+/.test(trimmed) || /^---+$/.test(trimmed)) {
      flush();
      continue;
    }

    if (/^#{3,}\s+/.test(trimmed)) {
      flush();
      continue;
    }

    if (/^\*{0,2}\[VISUAL:/i.test(trimmed)) {
      flush();
      continue;
    }

    currentLines.push(trimmed.replace(/^\*{0,2}NARRATOR:\*{0,2}\s*/i, ""));
  }

  flush();
  return paragraphs;
}

export function parseTimedNarrativeHeadings(mainScript: string): Array<{
  heading: string;
  narration: string[];
}> {
  const headingMatches = Array.from(mainScript.matchAll(/^##\s+(.+?)\s*$/gm));

  return headingMatches
    .map((match, index) => {
      const heading = collapseWhitespace(match[1] ?? "");
      const start = match.index ?? 0;
      const bodyStart = start + match[0].length;
      const bodyEnd = headingMatches[index + 1]?.index ?? mainScript.length;
      const body = mainScript.slice(bodyStart, bodyEnd);
      return {
        heading,
        narration: extractNarrationParagraphs(body),
      };
    })
    .filter((section) => section.heading.length > 0 && isTimedNarrativeHeading(section.heading));
}

export function buildNarrativeStructureManifest(
  mainScript: string,
  projectSections: ReadonlyArray<SectionHeadingOwner>,
): NarrativeStructureManifest {
  return buildNarrativeStructureManifestFromHeadings(
    parseTimedNarrativeHeadings(mainScript),
    projectSections,
  );
}

export function buildNarrativeStructureManifestFromHeadings(
  parsedSections: ReadonlyArray<{ heading: string; narration: string[] }>,
  projectSections: ReadonlyArray<SectionHeadingOwner>,
): NarrativeStructureManifest {
  const assignments = resolveNarrativeSectionAssignments(
    parsedSections,
    projectSections,
  );
  const seenSectionCounts = new Map<string, number>();

  return {
    headings: assignments.map((assignment, order) => {
      const seenCount = assignment.pipelineSectionId
        ? seenSectionCounts.get(assignment.pipelineSectionId) ?? 0
        : 0;

      if (assignment.pipelineSectionId) {
        seenSectionCounts.set(assignment.pipelineSectionId, seenCount + 1);
      }

      return {
        headingId: `${String(order + 1).padStart(2, "0")}_${headingSlug(assignment.heading) || "heading"}`,
        order,
        heading: assignment.heading,
        normalizedHeading: assignment.normalizedHeading,
        narration: assignment.narration,
        pipelineSectionId: assignment.pipelineSectionId,
        pipelineSectionLabel: assignment.pipelineSectionLabel,
        matchSource: assignment.matchSource,
        kind: !assignment.pipelineSectionId
          ? "unmatched"
          : seenCount === 0
            ? "section"
            : "folded_heading",
      };
    }),
  };
}

export function loadNarrativeStructureManifest(
  projectDir = getProjectDir(),
): NarrativeStructureManifest | null {
  const manifestPath = narrativeStructureManifestPath(projectDir);
  if (!fs.existsSync(manifestPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
    if (!parsed || !Array.isArray(parsed.headings)) {
      return null;
    }
    return parsed as NarrativeStructureManifest;
  } catch {
    return null;
  }
}

export function normalizeAndPersistNarrativeStructureManifest(params: {
  mainScript: string;
  projectSections: ReadonlyArray<SectionHeadingOwner>;
  projectDir?: string;
}): NarrativeStructureManifest {
  const {
    mainScript,
    projectSections,
    projectDir = getProjectDir(),
  } = params;
  const manifest = buildNarrativeStructureManifest(mainScript, projectSections);
  const manifestPath = narrativeStructureManifestPath(projectDir);
  const serialized = `${JSON.stringify(manifest, null, 2)}\n`;
  const current = fs.existsSync(manifestPath)
    ? fs.readFileSync(manifestPath, "utf-8")
    : null;

  if (current !== serialized) {
    fs.mkdirSync(path.dirname(manifestPath), { recursive: true });
    const tmpPath = `${manifestPath}.tmp`;
    fs.writeFileSync(tmpPath, serialized, "utf-8");
    fs.renameSync(tmpPath, manifestPath);
  }

  return manifest;
}

export function groupScriptSectionsByProjectSection<
  T extends NarrativeHeadingLike,
>(
  scriptSections: ReadonlyArray<T>,
  projectSections: ReadonlyArray<SectionHeadingOwner>,
  narrativeStructure?: NarrativeStructureManifest | null,
): Map<string, Array<AssignedNarrativeHeading<T>>> {
  const grouped = new Map<string, Array<AssignedNarrativeHeading<T>>>();
  const manifestAssignments =
    narrativeStructure &&
    narrativeStructure.headings.length === scriptSections.length
      ? scriptSections.map((section, index) => {
          const entry = narrativeStructure.headings[index];
          return {
            ...section,
            normalizedHeading: entry.normalizedHeading,
            pipelineSectionId: entry.pipelineSectionId,
            pipelineSectionLabel: entry.pipelineSectionLabel,
            matchSource: entry.matchSource,
          } as AssignedNarrativeHeading<T>;
        })
      : null;
  const assignments =
    manifestAssignments ??
    resolveNarrativeSectionAssignments(scriptSections, projectSections);

  assignments.forEach((assignment) => {
    if (!assignment.pipelineSectionId) {
      return;
    }
    const existing = grouped.get(assignment.pipelineSectionId) ?? [];
    existing.push(assignment);
    grouped.set(assignment.pipelineSectionId, existing);
  });

  return grouped;
}
