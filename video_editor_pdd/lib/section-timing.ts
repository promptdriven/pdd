import fs from "fs";
import path from "path";

import { loadLatestWordTimestamps } from "./audio-sync-artifacts";
import { normalizeSectionKey } from "./spec-script-context";

type SectionTimingTarget = {
  id: string;
  label?: string;
  durationSeconds?: number;
  offsetSeconds?: number;
};

type ScriptSectionTiming = {
  heading: string;
  normalizedHeading: string;
  startSeconds: number;
  endSeconds: number;
};

export type SectionNarrativeTiming = {
  offsetSeconds: number;
  durationSeconds: number;
  source: "audio-sync" | "script" | "project";
};

const SCRIPT_SECTION_RE = /^##\s+(.+?)\s*\(([0-9:.]+)\s*[-–—]\s*([0-9:.]+)\)\s*$/gm;

function parseClockTime(value: string): number | null {
  const trimmed = value.trim();
  if (!trimmed) {
    return null;
  }

  const parts = trimmed.split(":").map((part) => Number(part));
  if (parts.some((part) => Number.isNaN(part))) {
    return null;
  }

  if (parts.length === 1) {
    return parts[0] ?? null;
  }

  if (parts.length === 2) {
    return (parts[0] ?? 0) * 60 + (parts[1] ?? 0);
  }

  if (parts.length === 3) {
    return (parts[0] ?? 0) * 3600 + (parts[1] ?? 0) * 60 + (parts[2] ?? 0);
  }

  return null;
}

export function parseScriptSectionTimings(content: string): ScriptSectionTiming[] {
  const matches = Array.from(content.matchAll(SCRIPT_SECTION_RE));

  return matches
    .map((match) => {
      const heading = (match[1] ?? "").trim();
      const startSeconds = parseClockTime(match[2] ?? "");
      const endSeconds = parseClockTime(match[3] ?? "");
      if (!heading || startSeconds === null || endSeconds === null || endSeconds <= startSeconds) {
        return null;
      }

      return {
        heading,
        normalizedHeading: normalizeSectionKey(heading),
        startSeconds,
        endSeconds,
      } satisfies ScriptSectionTiming;
    })
    .filter((timing): timing is ScriptSectionTiming => Boolean(timing));
}

function buildSectionCandidates(section: SectionTimingTarget): string[] {
  return [section.label, section.id]
    .filter(Boolean)
    .map((value) => normalizeSectionKey(String(value)))
    .filter(Boolean);
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

export function findMatchingScriptSectionTiming(
  timings: ScriptSectionTiming[],
  section: SectionTimingTarget
): ScriptSectionTiming | null {
  const candidates = buildSectionCandidates(section);
  let bestMatch: ScriptSectionTiming | null = null;
  let bestScore = 0;

  timings.forEach((timing) => {
    candidates.forEach((candidate) => {
      const condensedHeading = timing.normalizedHeading.replace(/\s+/g, "");
      const condensedCandidate = candidate.replace(/\s+/g, "");

      let score = 0;
      if (timing.normalizedHeading === candidate) {
        score = 100;
      } else if (condensedHeading === condensedCandidate) {
        score = 95;
      } else if (
        timing.normalizedHeading.includes(candidate) ||
        candidate.includes(timing.normalizedHeading)
      ) {
        score = 80;
      } else {
        score = Math.round(tokenOverlapScore(timing.normalizedHeading, candidate) * 70);
      }

      if (score > bestScore) {
        bestScore = score;
        bestMatch = timing;
      }
    });
  });

  return bestScore >= 60 ? bestMatch : null;
}

function loadSectionAudioDuration(projectDir: string, sectionId: string): number | null {
  const words = loadLatestWordTimestamps(projectDir, sectionId);
  const maxEnd = words.reduce((maxValue, word) => {
    const end = typeof word?.end === "number" ? word.end : 0;
    return Math.max(maxValue, end);
  }, 0);
  return maxEnd > 0 ? maxEnd : null;
}

export function resolveSectionNarrativeTiming(
  projectDir: string,
  section: SectionTimingTarget
): SectionNarrativeTiming {
  let scriptTiming: ScriptSectionTiming | null = null;
  const mainScriptPath = path.join(projectDir, "narrative", "main_script.md");

  if (fs.existsSync(mainScriptPath)) {
    try {
      const scriptContent = fs.readFileSync(mainScriptPath, "utf-8");
      scriptTiming = findMatchingScriptSectionTiming(
        parseScriptSectionTimings(scriptContent),
        section
      );
    } catch {
      scriptTiming = null;
    }
  }

  const audioDurationSeconds = loadSectionAudioDuration(projectDir, section.id);
  if (audioDurationSeconds !== null) {
    return {
      offsetSeconds: scriptTiming?.startSeconds ?? section.offsetSeconds ?? 0,
      durationSeconds: audioDurationSeconds,
      source: "audio-sync",
    };
  }

  if (scriptTiming) {
    return {
      offsetSeconds: scriptTiming.startSeconds,
      durationSeconds: scriptTiming.endSeconds - scriptTiming.startSeconds,
      source: "script",
    };
  }

  return {
    offsetSeconds: section.offsetSeconds ?? 0,
    durationSeconds: section.durationSeconds ?? 0,
    source: "project",
  };
}
