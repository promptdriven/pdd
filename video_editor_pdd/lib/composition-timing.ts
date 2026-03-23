import fs from "fs";
import path from "path";
import { resolveSectionVisualContract } from "@/app/api/pipeline/_lib/visual-contract-manifest";
import { resolveSectionNarrativeTiming } from "./section-timing";

import {
  normalizeSpecTimestampRangeToSection,
  parseSpecTimestampRange,
} from "./spec-timestamp";
import type { Section } from "./types";

export {
  normalizeSpecTimestampRangeToSection,
  parseSpecTimestampRange,
} from "./spec-timestamp";

const DEFAULT_FPS = 30;
const DEFAULT_VISUAL_DURATION_SECONDS = 5;
const DEFAULT_KEYWORD_LEAD_SECONDS = 1;
const MIN_VISUAL_DURATION_SECONDS = 1 / DEFAULT_FPS;
const NON_COMPONENT_BASENAMES = new Set(["spec", "veo"]);
const VIDEO_PATH_RE = /["']([^"'\\\n]+\.(?:mp4|webm|mov|m4v))["']/gi;

type SectionComposition = NonNullable<Section["compositions"]>[number];

export type WordTimestamp = {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
};

export type TimingSource = "project" | "spec" | "audio-sync" | "fallback";

export type ResolvedVisualTiming = {
  id: string;
  startSeconds: number;
  endSeconds: number;
  source: TimingSource;
  desc: string;
  specPath?: string;
};

type SectionTimingTarget = Pick<Section, "id" | "specDir" | "durationSeconds" | "compositionId"> & {
  label?: Section["label"];
  offsetSeconds?: Section["offsetSeconds"];
  compositions?: Section["compositions"];
};

export type ResolvedSectionVisual = {
  id: string;
  specBaseName: string;
  specPath?: string;
  hasComponent: boolean;
  hasExplicitMedia: boolean;
  requiresCompositedAudit: boolean;
  previewCompositionId?: string;
  mediaReferences: string[];
  stagedAssetPath?: string;
  auditHints: AuditHints;
};

export type AuditTransitionWindow = {
  startFrame: number;
  endFrame: number;
  description: string;
};

export type AuditHints = {
  criticalElements: string[];
  decorativeElements: string[];
  layoutKeywords: string[];
  transitionWindows: AuditTransitionWindow[];
};

type TimingCandidate = {
  startSeconds: number;
  endSeconds?: number;
  source: Exclude<TimingSource, "fallback">;
  desc: string;
  specPath?: string;
};

function stripSpecsPrefix(specDir: string): string {
  return specDir.replace(/^specs[\\/]/, "").replace(/^[\\/]+/, "");
}

function resolveSectionSpecDir(projectDir: string, specDir: string): string {
  return path.isAbsolute(specDir)
    ? specDir
    : path.join(projectDir, "specs", stripSpecsPrefix(specDir));
}

function escapeDescription(value: string): string {
  return value.replace(/\\/g, "\\\\").replace(/"/g, '\\"');
}

function titleFromId(value: string): string {
  return value
    .replace(/^\d+[_-]?/, "")
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0]?.toUpperCase() + part.slice(1))
    .join(" ");
}

function componentBaseName(componentId: string, sectionId: string): string {
  const prefix = `${sectionId}_`;
  return componentId.startsWith(prefix) ? componentId.slice(prefix.length) : componentId;
}

function toPascalCase(value: string): string {
  return value
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0]?.toUpperCase() + part.slice(1))
    .join("");
}

export function resolvePreviewCompositionId(
  componentId: string,
  sectionId: string
): string {
  let componentPascal = toPascalCase(componentId);
  if (componentPascal && /^\d/.test(componentPascal)) {
    componentPascal = `${toPascalCase(sectionId)}${componentPascal}`;
  }

  return componentPascal
    .replace(/([a-z0-9])([A-Z])/g, "$1-$2")
    .toLowerCase();
}

const SPEC_MEDIA_RE =
  /\b(?:clipSource|leftClip|rightClip|leftSrc|rightSrc|outputSrc|backgroundClip|backgroundSrc|baseClip|baseSrc|revealClip|revealSrc)\b/i;
const STATIC_FILE_RE = /staticFile\(\s*["'][^"']+\.(?:mp4|webm|mov|m4v)["']\s*\)/i;
const GENERIC_MEDIA_RE = /\.(?:mp4|webm|mov|m4v)\b/i;
const JSX_COMPONENT_TAG_RE = /<([A-Z][A-Za-z0-9]*)\b/g;
const COMPOSITED_MEDIA_HINT_RE =
  /\b(lower-third|narration badge|narration text|voice badge|caption|subtitle|gradient overlay|light bloom|overlay|badge|label|rule)\b/i;
const Z_INDEX_OVERLAY_RE = /z-index\s*[1-9]/i;
const BULLET_BOLD_LABEL_RE =
  /^\s*(?:[-*]|\d+\.)\s+\*\*(.+?)\*\*(?:\s*[—–-]\s*|:\s*)?(.*)$/gm;
const ANIMATION_FRAME_RANGE_RE =
  /Frames?\s+(\d+)\s*[–-]\s*(\d+)(?:\s*\([^)]*\))?\s*:\s*(.+)$/gim;
const DECORATIVE_HINT_RE =
  /\b(glow(?:ing)?|shadow|blur|bloom|trail|streak|separator|rule|gradient|flare|accent|particle|halo|grid|texture)\b/i;
const LAYOUT_PHRASES = [
  "split-screen",
  "side-by-side",
  "centered",
  "center",
  "bottom-center",
  "bottom center",
  "top-center",
  "top center",
  "left panel",
  "right panel",
  "lower-third",
  "overlay",
  "divider",
  "full-bleed",
  "full-frame",
] as const;
const AUDIT_HINT_METADATA_LABELS = new Set([
  "tool",
  "duration",
  "timestamp",
  "resolution",
  "background",
  "easing",
]);

function requiresCompositedMediaAudit(content: string): boolean {
  if (!GENERIC_MEDIA_RE.test(content)) {
    return false;
  }

  for (const match of content.matchAll(JSX_COMPONENT_TAG_RE)) {
    const tagName = match[1];
    if (!tagName) {
      continue;
    }

    if (!["AbsoluteFill", "Sequence", "OffthreadVideo", "Audio"].includes(tagName)) {
      return true;
    }
  }

  return (
    COMPOSITED_MEDIA_HINT_RE.test(content) ||
    (Z_INDEX_OVERLAY_RE.test(content) && /\b(text|overlay|badge|label|caption|subtitle|bloom|rule)\b/i.test(content))
  );
}

export function extractSpecMediaReferences(content: string): string[] {
  const references: string[] = [];

  for (const match of content.matchAll(VIDEO_PATH_RE)) {
    const rawPath = match[1]?.trim();
    if (!rawPath) {
      continue;
    }

    const normalized = rawPath.replace(/\\/g, "/").replace(/^\.?\//, "");
    if (!references.includes(normalized)) {
      references.push(normalized);
    }
  }

  return references;
}

function pushUnique(values: string[], nextValue: string): void {
  const trimmed = nextValue.trim();
  if (!trimmed || values.includes(trimmed)) {
    return;
  }

  values.push(trimmed);
}

export function resolveSpecAuditHints(content: string): AuditHints {
  const criticalElements: string[] = [];
  const decorativeElements: string[] = [];
  const layoutKeywords: string[] = [];
  const transitionWindows: AuditTransitionWindow[] = [];

  for (const match of content.matchAll(BULLET_BOLD_LABEL_RE)) {
    const label = match[1]?.trim();
    const detail = match[2]?.trim() ?? "";
    if (!label) {
      continue;
    }

    const normalizedLabel = label.toLowerCase();
    if (AUDIT_HINT_METADATA_LABELS.has(normalizedLabel)) {
      continue;
    }

    const combined = `${label} ${detail}`.trim();
    if (DECORATIVE_HINT_RE.test(combined)) {
      pushUnique(decorativeElements, label);
    } else {
      pushUnique(criticalElements, label);
    }
  }

  const lowerContent = content.toLowerCase();
  for (const phrase of LAYOUT_PHRASES) {
    if (lowerContent.includes(phrase)) {
      pushUnique(layoutKeywords, phrase);
    }
  }

  for (const match of content.matchAll(ANIMATION_FRAME_RANGE_RE)) {
    const startFrame = Number(match[1]);
    const endFrame = Number(match[2]);
    const description = match[3]?.replace(/\*\*/g, "").trim();
    if (Number.isNaN(startFrame) || Number.isNaN(endFrame) || !description) {
      continue;
    }

    transitionWindows.push({
      startFrame,
      endFrame,
      description,
    });
  }

  return {
    criticalElements,
    decorativeElements,
    layoutKeywords,
    transitionWindows,
  };
}

function listSectionSpecBaseNames(
  projectDir: string,
  section: Pick<SectionTimingTarget, "id" | "specDir">
): string[] {
  if (!section.specDir) {
    return [];
  }

  const specDir = resolveSectionSpecDir(projectDir, section.specDir);
  if (!fs.existsSync(specDir)) {
    return [];
  }

  try {
    return fs
      .readdirSync(specDir)
      .filter((entry) => entry.endsWith(".md") && !entry.startsWith("AUDIT_"))
      .map((entry) => path.basename(entry, path.extname(entry)))
      .filter((baseName) => !NON_COMPONENT_BASENAMES.has(baseName))
      .sort((left, right) => left.localeCompare(right));
  } catch {
    return [];
  }
}

function listCompositionIds(section: SectionTimingTarget, componentIds: string[]): string[] {
  const configuredIds = (section.compositions ?? [])
    .map((composition) =>
      typeof composition === "string" ? composition : composition?.id
    )
    .filter((compositionId): compositionId is string => Boolean(compositionId));

  const merged = [...configuredIds, ...componentIds];
  const seen = new Set<string>();

  return merged.filter((compositionId) => {
    if (seen.has(compositionId)) {
      return false;
    }

    seen.add(compositionId);
    return true;
  });
}

function resolveSpecMediaInfo(
  projectDir: string,
  section: Pick<SectionTimingTarget, "id" | "specDir">,
  specBaseName: string
): {
  specPath?: string;
  hasExplicitMedia: boolean;
  hasSpecReferencedMedia: boolean;
  requiresCompositedAudit: boolean;
  mediaReferences: string[];
  stagedAssetPath?: string;
  auditHints: AuditHints;
} {
  const visualContract = resolveSectionVisualContract(
    section.id,
    specBaseName,
    projectDir
  );
  const contractMediaReferences = Array.from(
    new Set(Object.values(visualContract?.mediaAliases ?? {}))
  );
  const contractRenderMode = visualContract?.renderMode;
  const contractPrimaryMedia = contractMediaReferences[0];
  const contractStagedAssetPath = contractPrimaryMedia
    ? path.join(projectDir, "remotion", "public", contractPrimaryMedia)
    : undefined;

  if (!section.specDir) {
    return {
      hasExplicitMedia: contractMediaReferences.length > 0,
      hasSpecReferencedMedia: false,
      requiresCompositedAudit:
        contractRenderMode === "generated-media" ||
        Boolean(visualContract?.overlayConfig),
      mediaReferences: contractMediaReferences,
      stagedAssetPath:
        contractStagedAssetPath && fs.existsSync(contractStagedAssetPath)
          ? contractStagedAssetPath
          : undefined,
      auditHints: resolveSpecAuditHints(""),
    };
  }

  const specDir = resolveSectionSpecDir(projectDir, section.specDir);
  const specPath = path.join(specDir, `${specBaseName}.md`);
  const stagedCandidates = [
    path.join(projectDir, "outputs", "veo", `${specBaseName}.mp4`),
    path.join(projectDir, "remotion", "public", "veo", `${specBaseName}.mp4`),
  ];
  const stagedAssetPath = stagedCandidates.find((candidate) => fs.existsSync(candidate));

  const hasStagedAsset = Boolean(stagedAssetPath);
  if (!fs.existsSync(specPath)) {
    return {
      specPath: undefined,
      hasExplicitMedia: hasStagedAsset || contractMediaReferences.length > 0,
      hasSpecReferencedMedia: false,
      requiresCompositedAudit:
        contractRenderMode === "generated-media" ||
        Boolean(visualContract?.overlayConfig),
      mediaReferences:
        contractMediaReferences.length > 0
          ? contractMediaReferences
          : stagedAssetPath
            ? [`veo/${specBaseName}.mp4`]
            : [],
      stagedAssetPath:
        stagedAssetPath ??
        (contractStagedAssetPath && fs.existsSync(contractStagedAssetPath)
          ? contractStagedAssetPath
          : undefined),
      auditHints: resolveSpecAuditHints(""),
    };
  }

  const content = fs.readFileSync(specPath, "utf-8");
  const mediaReferences = extractSpecMediaReferences(content);
  const hasSpecReferencedMedia =
    SPEC_MEDIA_RE.test(content) ||
    STATIC_FILE_RE.test(content) ||
    GENERIC_MEDIA_RE.test(content);
  const requiresCompositedAudit = requiresCompositedMediaAudit(content);
  return {
    specPath,
    hasExplicitMedia:
      hasStagedAsset ||
      hasSpecReferencedMedia ||
      contractMediaReferences.length > 0,
    hasSpecReferencedMedia,
    requiresCompositedAudit:
      requiresCompositedAudit ||
      contractRenderMode === "generated-media" ||
      Boolean(visualContract?.overlayConfig),
    mediaReferences: Array.from(
      new Set(
        [
          ...mediaReferences,
          ...contractMediaReferences,
          stagedAssetPath ? `veo/${specBaseName}.mp4` : null,
        ].filter((value): value is string => Boolean(value))
      )
    ),
    stagedAssetPath:
      stagedAssetPath ??
      (contractStagedAssetPath && fs.existsSync(contractStagedAssetPath)
        ? contractStagedAssetPath
        : undefined),
    auditHints: resolveSpecAuditHints(content),
  };
}

const SPLIT_MARKER_RE = /^\s*\[split:[^\]]*\]/i;
const DATA_POINTS_JSON_RE =
  /(?:^|\n)##\s*Data Points(?:\s+JSON)?\s*(?:\r?\n)+```json\s*([\s\S]+?)\s*```/i;

function collectEmbeddedCompanionIds(
  projectDir: string,
  section: Pick<SectionTimingTarget, "id" | "specDir">
): Set<string> {
  const companionIds = new Set<string>();
  if (!section.specDir) return companionIds;

  const specDir = resolveSectionSpecDir(projectDir, section.specDir);
  if (!fs.existsSync(specDir)) return companionIds;

  for (const entry of fs.readdirSync(specDir, { withFileTypes: true })) {
    if (!entry.isFile() || !entry.name.endsWith(".md")) continue;

    let content: string;
    try {
      content = fs.readFileSync(path.join(specDir, entry.name), "utf-8");
    } catch {
      continue;
    }

    if (!SPLIT_MARKER_RE.test(content)) continue;

    const match = DATA_POINTS_JSON_RE.exec(content);
    if (!match?.[1]) continue;

    let dataPoints: Record<string, unknown>;
    try {
      dataPoints = JSON.parse(match[1]);
    } catch {
      continue;
    }

    const collect = (value: unknown): void => {
      if (value && typeof value === "object" && !Array.isArray(value)) {
        for (const [key, nested] of Object.entries(value as Record<string, unknown>)) {
          const normalized = key.replace(/[_-]/g, "").toLowerCase();
          if (
            (normalized === "leftclipid" || normalized === "rightclipid" ||
             normalized === "clipid" || normalized === "content") &&
            typeof nested === "string" && nested.trim()
          ) {
            companionIds.add(nested.trim());
          } else if (typeof nested === "object" && nested !== null) {
            collect(nested);
          }
        }
      }
    };

    collect(dataPoints);
  }

  return companionIds;
}

function isEmbeddedCompanion(specBaseName: string, companionIds: Set<string>): boolean {
  if (companionIds.size === 0) return false;

  const stripped = specBaseName.replace(/^\d+_/, "");
  const normalizedBase = specBaseName.replace(/[_-]/g, "").toLowerCase();
  const normalizedStripped = stripped.replace(/[_-]/g, "").toLowerCase();

  for (const id of companionIds) {
    const normalizedId = id.replace(/[_-]/g, "").toLowerCase();
    if (
      normalizedBase === normalizedId ||
      normalizedStripped === normalizedId ||
      normalizedBase.includes(normalizedId) ||
      normalizedStripped.includes(normalizedId)
    ) {
      return true;
    }
  }

  return false;
}

export function resolveSectionVisuals(
  projectDir: string,
  section: SectionTimingTarget,
  componentIds: string[]
): ResolvedSectionVisual[] {
  const specBaseNames = listSectionSpecBaseNames(projectDir, section);
  const configuredIds = listCompositionIds(section, componentIds);
  const consumedCompositionIds = new Set<string>();
  const resolvedVisuals: ResolvedSectionVisual[] = [];
  const companionIds = collectEmbeddedCompanionIds(projectDir, section);

  for (const specBaseName of specBaseNames) {
    const matchingCompositionId = configuredIds.find((compositionId) => {
      return componentBaseName(compositionId, section.id) === specBaseName;
    });

    const mediaInfo = resolveSpecMediaInfo(
      projectDir,
      section,
      specBaseName
    );

    if (matchingCompositionId) {
      consumedCompositionIds.add(matchingCompositionId);
      resolvedVisuals.push({
        id: matchingCompositionId,
        specBaseName,
        specPath: path.join(resolveSectionSpecDir(projectDir, section.specDir), `${specBaseName}.md`),
        hasComponent: true,
        hasExplicitMedia: mediaInfo.hasExplicitMedia,
        requiresCompositedAudit: mediaInfo.requiresCompositedAudit,
        previewCompositionId: resolvePreviewCompositionId(
          matchingCompositionId,
          section.id
        ),
        mediaReferences: mediaInfo.hasExplicitMedia
          ? mediaInfo.mediaReferences
          : [],
        stagedAssetPath: mediaInfo.stagedAssetPath,
        auditHints: mediaInfo.auditHints,
      });
      continue;
    }

    if (!mediaInfo.hasExplicitMedia) {
      continue;
    }

    // Skip companion veo specs embedded in a parent [split:] — the parent
    // component already renders them; they shouldn't occupy timeline slots.
    if (isEmbeddedCompanion(specBaseName, companionIds)) {
      continue;
    }

    resolvedVisuals.push({
      id: specBaseName,
      specBaseName,
      specPath: mediaInfo.specPath,
      hasComponent: false,
      hasExplicitMedia: true,
      requiresCompositedAudit: mediaInfo.requiresCompositedAudit,
      mediaReferences: mediaInfo.mediaReferences,
      stagedAssetPath: mediaInfo.stagedAssetPath,
      auditHints: mediaInfo.auditHints,
    });
  }

  for (const compositionId of configuredIds) {
    if (consumedCompositionIds.has(compositionId)) {
      continue;
    }

    const specBaseName = componentBaseName(compositionId, section.id);
    const specPath = section.specDir
      ? path.join(resolveSectionSpecDir(projectDir, section.specDir), `${specBaseName}.md`)
      : undefined;

    resolvedVisuals.push({
      id: compositionId,
      specBaseName,
      specPath: specPath && fs.existsSync(specPath) ? specPath : undefined,
      hasComponent: true,
      hasExplicitMedia: false,
      requiresCompositedAudit: false,
      previewCompositionId: resolvePreviewCompositionId(compositionId, section.id),
      mediaReferences: [],
      auditHints:
        specPath && fs.existsSync(specPath)
          ? resolveSpecAuditHints(fs.readFileSync(specPath, "utf-8"))
          : resolveSpecAuditHints(""),
    });
  }

  return resolvedVisuals;
}

export function listSectionVisualIds(
  projectDir: string,
  section: SectionTimingTarget,
  componentIds: string[]
): string[] {
  return resolveSectionVisuals(projectDir, section, componentIds).map(
    (visual) => visual.id
  );
}

function readSpecContent(projectDir: string, section: SectionTimingTarget, componentId: string): {
  path?: string;
  content?: string;
} {
  if (!section.specDir) {
    return {};
  }

  const specDir = resolveSectionSpecDir(projectDir, section.specDir);
  const baseName = componentBaseName(componentId, section.id);

  for (const extension of [".md", ".txt"]) {
    const candidate = path.join(specDir, `${baseName}${extension}`);
    if (!fs.existsSync(candidate)) {
      continue;
    }

    try {
      return {
        path: candidate,
        content: fs.readFileSync(candidate, "utf-8"),
      };
    } catch {
      return {};
    }
  }

  return {};
}

function parseSpecHeading(content: string, componentId: string): string {
  const match = content.match(/^#\s+(.+)$/m);
  return match?.[1]?.trim() || titleFromId(componentId);
}

function loadWordTimestamps(projectDir: string, sectionId: string): WordTimestamp[] {
  const timestampsPath = path.join(
    projectDir,
    "outputs",
    "tts",
    sectionId,
    "word_timestamps.json"
  );

  if (!fs.existsSync(timestampsPath)) {
    return [];
  }

  try {
    const raw = fs.readFileSync(timestampsPath, "utf-8");
    const parsed = JSON.parse(raw);
    const words = Array.isArray(parsed) ? parsed : Array.isArray(parsed?.words) ? parsed.words : [];
    return words.filter((word: unknown): word is WordTimestamp => {
      return (
        typeof (word as WordTimestamp | undefined)?.word === "string" &&
        typeof (word as WordTimestamp | undefined)?.start === "number" &&
        typeof (word as WordTimestamp | undefined)?.end === "number"
      );
    });
  } catch {
    return [];
  }
}

function extractKeyword(componentId: string, sectionId: string): {
  keyword: string;
  type: "stat_callout" | "split" | "title_card" | "main" | "other";
} {
  const rawSuffix = componentId.startsWith(`${sectionId}_`)
    ? componentId.slice(sectionId.length + 1)
    : componentId;
  const suffix = rawSuffix.replace(/^\d+[_-]?/, "");

  if (suffix === "title_card" || suffix === "main") {
    return { keyword: "", type: suffix };
  }

  if (suffix.startsWith("stat_callout_")) {
    return {
      keyword: suffix.replace(/^stat_callout_/, ""),
      type: "stat_callout",
    };
  }

  if (suffix.startsWith("split_")) {
    const pieces = suffix.replace(/^split_/, "").split("_vs_");
    const keyword = (pieces.length > 1 ? pieces[pieces.length - 1] : pieces[0] || "")
      .replace(/_/g, " ");
    return { keyword, type: "split" };
  }

  return { keyword: suffix, type: "other" };
}

function normalizeWord(value: string): string {
  return value.replace(/[.,!?;:'"()]+/g, "").toLowerCase();
}

function findKeywordTimestamp(keyword: string, words: WordTimestamp[]): number | null {
  const keywordLower = keyword.toLowerCase();
  const condensedKeyword = keywordLower.replace(/_/g, "");

  for (const word of words) {
    if (normalizeWord(word.word) === condensedKeyword) {
      return word.start;
    }
  }

  if (condensedKeyword.length >= 4) {
    for (const word of words) {
      if (normalizeWord(word.word).includes(condensedKeyword)) {
        return word.start;
      }
    }
  }

  if (keywordLower.includes("_")) {
    const parts = keywordLower.split("_").filter((part) => part.length >= 4);
    for (const part of parts) {
      for (const word of words) {
        if (normalizeWord(word.word) === part) {
          return word.start;
        }
      }
    }
  }

  return null;
}

function resolveProjectCompositionTiming(
  section: SectionTimingTarget,
  componentId: string
): TimingCandidate | null {
  const composition = (section.compositions ?? []).find((entry) => {
    if (typeof entry === "string") {
      return entry === componentId;
    }

    return entry?.id === componentId;
  });

  if (
    !composition ||
    typeof composition === "string" ||
    typeof composition.startSeconds !== "number"
  ) {
    return null;
  }

  const durationSeconds =
    typeof composition.durationSeconds === "number" && composition.durationSeconds > 0
      ? composition.durationSeconds
      : undefined;

  return {
    startSeconds: composition.startSeconds,
    endSeconds:
      durationSeconds !== undefined ? composition.startSeconds + durationSeconds : undefined,
    source: "project",
    desc: titleFromId(componentId),
  };
}

function resolveAudioTimingCandidate(
  words: WordTimestamp[],
  section: SectionTimingTarget,
  componentId: string,
  sectionDurationSeconds: number
): TimingCandidate | null {
  const { keyword, type } = extractKeyword(componentId, section.id);

  if (type === "title_card") {
    return {
      startSeconds: 0,
      endSeconds: DEFAULT_VISUAL_DURATION_SECONDS,
      source: "audio-sync",
      desc: titleFromId(componentId),
    };
  }

  if (type === "main") {
    return {
      startSeconds: 0,
      endSeconds: sectionDurationSeconds,
      source: "audio-sync",
      desc: titleFromId(componentId),
    };
  }

  if (!keyword || words.length === 0) {
    return null;
  }

  const match = findKeywordTimestamp(keyword, words);
  if (match === null) {
    return null;
  }

  const startSeconds = Math.max(0, match - DEFAULT_KEYWORD_LEAD_SECONDS);
  return {
    startSeconds,
    endSeconds: startSeconds + DEFAULT_VISUAL_DURATION_SECONDS,
    source: "audio-sync",
    desc: titleFromId(componentId),
  };
}

function buildTimingCandidates(
  projectDir: string,
  section: SectionTimingTarget,
  componentIds: string[],
  sectionNarrativeTiming: { durationSeconds: number; offsetSeconds: number }
): Array<TimingCandidate | null> {
  const words = loadWordTimestamps(projectDir, section.id);

  return componentIds.map((componentId) => {
    const projectTiming = resolveProjectCompositionTiming(section, componentId);
    if (projectTiming) {
      return projectTiming;
    }

    const { path: specPath, content: specContent } = readSpecContent(projectDir, section, componentId);
    if (specContent) {
      const range = parseSpecTimestampRange(specContent);
      if (range) {
        const normalizedRange = normalizeSpecTimestampRangeToSection(
          range,
          sectionNarrativeTiming.durationSeconds,
          sectionNarrativeTiming.offsetSeconds
        );
        return {
          startSeconds: normalizedRange.startSeconds,
          endSeconds: normalizedRange.endSeconds,
          source: "spec",
          desc: parseSpecHeading(specContent, componentId),
          specPath,
        };
      }
    }

    return resolveAudioTimingCandidate(
      words,
      section,
      componentId,
      sectionNarrativeTiming.durationSeconds
    );
  });
}

function scaleSpecCandidatesToSectionDuration(
  candidates: Array<TimingCandidate | null>,
  sectionDurationSeconds: number
): Array<TimingCandidate | null> {
  if (sectionDurationSeconds <= 0) {
    return candidates;
  }

  const maxSpecEnd = candidates.reduce((maxValue, candidate) => {
    if (!candidate || candidate.source !== "spec") {
      return maxValue;
    }

    return Math.max(maxValue, candidate.endSeconds ?? candidate.startSeconds);
  }, 0);

  if (maxSpecEnd <= sectionDurationSeconds || maxSpecEnd <= 0) {
    return candidates;
  }

  // Within 15% tolerance: clamp end times instead of scaling all timestamps.
  // This preserves accurate word-timestamp-derived specs while still scaling
  // obviously-wrong script-timeline specs (typically 2-10x too large).
  if (maxSpecEnd <= sectionDurationSeconds * 1.15) {
    return candidates.map((candidate) => {
      if (!candidate || candidate.source !== "spec") {
        return candidate;
      }

      return {
        ...candidate,
        startSeconds: Math.min(candidate.startSeconds, sectionDurationSeconds),
        endSeconds: Math.min(
          candidate.endSeconds ?? candidate.startSeconds + MIN_VISUAL_DURATION_SECONDS,
          sectionDurationSeconds
        ),
      };
    });
  }

  const scale = sectionDurationSeconds / maxSpecEnd;
  return candidates.map((candidate) => {
    if (!candidate || candidate.source !== "spec") {
      return candidate;
    }

    return {
      ...candidate,
      startSeconds: candidate.startSeconds * scale,
      endSeconds:
        (candidate.endSeconds ?? candidate.startSeconds + MIN_VISUAL_DURATION_SECONDS) * scale,
    };
  });
}

function effectiveSectionDuration(
  sectionDurationSeconds: number,
  candidates: Array<TimingCandidate | null>,
  componentCount: number
): number {
  if (sectionDurationSeconds > 0) {
    return sectionDurationSeconds;
  }

  const fromCandidates = candidates.reduce((maxValue, candidate) => {
    return Math.max(
      maxValue,
      candidate?.endSeconds ?? candidate?.startSeconds ?? 0
    );
  }, 0);

  return Math.max(
    fromCandidates,
    componentCount * MIN_VISUAL_DURATION_SECONDS
  );
}

function buildFallbackTimings(
  componentIds: string[],
  candidates: Array<TimingCandidate | null>,
  sectionDurationSeconds: number
): ResolvedVisualTiming[] {
  const resolved: ResolvedVisualTiming[] = [];
  let previousEnd = 0;
  let index = 0;

  while (index < componentIds.length) {
    const candidate = candidates[index];
    if (candidate) {
      resolved.push({
        id: componentIds[index],
        startSeconds: candidate.startSeconds,
        endSeconds: candidate.endSeconds ?? candidate.startSeconds + DEFAULT_VISUAL_DURATION_SECONDS,
        source: candidate.source,
        desc: candidate.desc,
        specPath: candidate.specPath,
      });
      previousEnd = candidate.endSeconds ?? candidate.startSeconds;
      index += 1;
      continue;
    }

    let blockEnd = index;
    while (blockEnd < componentIds.length && !candidates[blockEnd]) {
      blockEnd += 1;
    }

    const nextCandidateStart =
      blockEnd < componentIds.length
        ? candidates[blockEnd]?.startSeconds ?? sectionDurationSeconds
        : sectionDurationSeconds;

    const untimedCount = blockEnd - index;
    const windowStart = Math.min(previousEnd, sectionDurationSeconds);
    const available = Math.max(
      untimedCount * MIN_VISUAL_DURATION_SECONDS,
      nextCandidateStart - windowStart
    );
    const slice = available / Math.max(untimedCount, 1);

    for (let offset = 0; offset < untimedCount; offset += 1) {
      const startSeconds = windowStart + slice * offset;
      const endSeconds = windowStart + slice * (offset + 1);
      resolved.push({
        id: componentIds[index + offset],
        startSeconds,
        endSeconds,
        source: "fallback",
        desc: titleFromId(componentIds[index + offset]),
      });
    }

    previousEnd = windowStart + available;
    index = blockEnd;
  }

  return resolved;
}

function normalizeVisualTimings(
  timings: ResolvedVisualTiming[],
  sectionDurationSeconds: number
): ResolvedVisualTiming[] {
  if (timings.length === 0) {
    return [];
  }

  const normalizedStarts: number[] = [];

  timings.forEach((timing, index) => {
    const remainingItems = timings.length - index - 1;
    const latestStart = Math.max(
      0,
      sectionDurationSeconds - MIN_VISUAL_DURATION_SECONDS * (remainingItems + 1)
    );
    const minimumStart =
      index === 0 ? 0 : normalizedStarts[index - 1] + MIN_VISUAL_DURATION_SECONDS;
    const clampedStart = Math.min(
      Math.max(timing.startSeconds, minimumStart),
      latestStart
    );
    normalizedStarts.push(clampedStart);
  });

  return timings.map((timing, index) => {
    const startSeconds = normalizedStarts[index];
    const endSeconds =
      index === timings.length - 1
        ? sectionDurationSeconds
        : normalizedStarts[index + 1];

    return {
      ...timing,
      startSeconds,
      endSeconds: Math.max(endSeconds, startSeconds + MIN_VISUAL_DURATION_SECONDS),
    };
  });
}

function shouldSequentializeTimings(timings: ResolvedVisualTiming[]): boolean {
  if (timings.length <= 1) {
    return false;
  }

  for (let index = 1; index < timings.length; index += 1) {
    const previous = timings[index - 1];
    const current = timings[index];
    if (current.startSeconds < previous.endSeconds - MIN_VISUAL_DURATION_SECONDS / 2) {
      return true;
    }
  }

  return false;
}

function sequentializeTimings(
  timings: ResolvedVisualTiming[],
  sectionDurationSeconds: number
): ResolvedVisualTiming[] {
  if (timings.length === 0 || sectionDurationSeconds <= 0) {
    return timings;
  }

  const desiredDurations = timings.map((timing) =>
    Math.max(MIN_VISUAL_DURATION_SECONDS, timing.endSeconds - timing.startSeconds)
  );
  const totalDesired = desiredDurations.reduce((sum, value) => sum + value, 0);
  const scale = totalDesired > 0 ? sectionDurationSeconds / totalDesired : 1;
  let cursor = 0;

  return timings.map((timing, index) => {
    const remaining = timings.length - index - 1;
    const minimumRemaining = remaining * MIN_VISUAL_DURATION_SECONDS;
    const desiredDuration = Math.max(
      MIN_VISUAL_DURATION_SECONDS,
      desiredDurations[index] * scale
    );
    const startSeconds = cursor;
    const unclampedEnd =
      index === timings.length - 1
        ? sectionDurationSeconds
        : Math.min(sectionDurationSeconds - minimumRemaining, startSeconds + desiredDuration);
    const endSeconds = Math.max(
      Math.min(sectionDurationSeconds, unclampedEnd),
      startSeconds + MIN_VISUAL_DURATION_SECONDS
    );
    cursor = endSeconds;

    return {
      ...timing,
      startSeconds,
      endSeconds,
    };
  });
}

export function resolveSectionVisualTimings(
  projectDir: string,
  section: SectionTimingTarget,
  componentIds: string[]
): ResolvedVisualTiming[] {
  const visualIds = listSectionVisualIds(projectDir, section, componentIds);
  const sectionNarrativeTiming = resolveSectionNarrativeTiming(projectDir, section);
  const candidates = scaleSpecCandidatesToSectionDuration(
    buildTimingCandidates(projectDir, section, visualIds, sectionNarrativeTiming),
    sectionNarrativeTiming.durationSeconds
  );
  const durationSeconds = effectiveSectionDuration(
    sectionNarrativeTiming.durationSeconds,
    candidates,
    visualIds.length
  );
  const seededTimings = buildFallbackTimings(visualIds, candidates, durationSeconds);
  const linearizedTimings = shouldSequentializeTimings(seededTimings)
    ? sequentializeTimings(seededTimings, durationSeconds)
    : seededTimings;

  return normalizeVisualTimings(linearizedTimings, durationSeconds);
}

export function buildSectionConstantsSource(
  projectDir: string,
  section: SectionTimingTarget,
  componentIds: string[],
  fps = DEFAULT_FPS
): string {
  const timings = resolveSectionVisualTimings(projectDir, section, componentIds);
  const sectionNarrativeTiming = resolveSectionNarrativeTiming(projectDir, section);
  const durationSeconds =
    timings[timings.length - 1]?.endSeconds ??
    Math.max(
      sectionNarrativeTiming.durationSeconds,
      componentIds.length * MIN_VISUAL_DURATION_SECONDS
    );
  const exportName = section.compositionId
    ? section.compositionId
        .split(/[_-]+/)
        .filter(Boolean)
        .map((part) => part[0]?.toUpperCase() + part.slice(1))
        .join("")
    : titleFromId(section.id).replace(/\s+/g, "");

  const beatLines: string[] = [];
  const visualLines: string[] = [];

  timings.forEach((timing, index) => {
    const key = String(index).padStart(2, "0");
    beatLines.push(`  VISUAL_${key}_START: s2f(${timing.startSeconds.toFixed(3)}),`);
    beatLines.push(`  VISUAL_${key}_END: s2f(${timing.endSeconds.toFixed(3)}),`);
    visualLines.push(
      `  { start: BEATS.VISUAL_${key}_START, end: BEATS.VISUAL_${key}_END, id: "${timing.id}", desc: "${escapeDescription(timing.desc)}" },`
    );
  });

  return `import { z } from "zod";

export const SECTION_FPS = ${fps};
export const SECTION_DURATION_SECONDS = ${durationSeconds.toFixed(3)};
export const SECTION_DURATION_FRAMES = Math.ceil(SECTION_FPS * SECTION_DURATION_SECONDS);

const s2f = (seconds: number) => Math.round(seconds * SECTION_FPS);

export const BEATS = {
${beatLines.join("\n")}
};

export const VISUAL_SEQUENCE = [
${visualLines.join("\n")}
];

export const ${exportName}Props = z.object({
  showTitle: z.boolean().default(true),
});

export const default${exportName}Props: z.infer<typeof ${exportName}Props> = {
  showTitle: true,
};

export type ${exportName}PropsType = z.infer<typeof ${exportName}Props>;
`;
}
