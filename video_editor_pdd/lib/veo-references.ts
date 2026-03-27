import fs from "fs";
import path from "path";

import type { ProjectConfig, Section, VeoFrameChain, VeoReference } from "./types";
import {
  extractMarkdownJsonBlock,
  extractVeoClipFilename,
  isVeoMarkdownSpec,
  normalizeSpecDir,
} from "./veo-spec-context";

type MarkdownSpecEntry = {
  sectionId: string;
  path: string;
  content: string;
};

type InferredVeoCharacterUsage = {
  sectionId: string;
  path: string;
  clipId: string;
  characterId: string;
  order: number;
};

type VeoCharacterContract = {
  id?: unknown;
  label?: unknown;
  referencePrompt?: unknown;
  prompt?: unknown;
  appearance?: unknown;
  description?: unknown;
};

function humanizeReferenceId(value: string): string {
  return value
    .split(/[_-]+/)
    .filter(Boolean)
    .map((token) => token[0].toUpperCase() + token.slice(1))
    .join(" ");
}

function normalizeReferenceId(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}

function uniqueSorted(values: string[]): string[] {
  return Array.from(new Set(values)).sort((left, right) => left.localeCompare(right));
}

function coerceCharacterPrompt(character: VeoCharacterContract): string | null {
  const candidates = [
    character.referencePrompt,
    character.prompt,
    character.appearance,
    character.description,
  ];

  for (const candidate of candidates) {
    if (typeof candidate === "string" && candidate.trim().length > 0) {
      return candidate.trim();
    }
  }

  return null;
}

function extractVeoCharacters(content: string): Array<{
  id: string;
  label: string;
  prompt: string | null;
}> {
  const dataPoints = extractMarkdownJsonBlock(content, "Data Points");
  const characters = Array.isArray(dataPoints?.characters)
    ? (dataPoints.characters as VeoCharacterContract[])
    : Array.isArray(dataPoints?.characterReferences)
      ? (dataPoints.characterReferences as VeoCharacterContract[])
      : [];

  return characters
    .map((character) => {
      const rawId =
        typeof character.id === "string" && character.id.trim().length > 0
          ? character.id.trim()
          : typeof character.label === "string" && character.label.trim().length > 0
            ? character.label.trim()
            : null;

      if (!rawId) {
        return null;
      }

      const id = normalizeReferenceId(rawId);
      if (!id) {
        return null;
      }

      const explicitLabel =
        typeof character.label === "string" && character.label.trim().length > 0
          ? character.label.trim()
          : null;

      return {
        id,
        label: explicitLabel ?? humanizeReferenceId(id),
        prompt: coerceCharacterPrompt(character),
      };
    })
    .filter((character): character is { id: string; label: string; prompt: string | null } => character !== null);
}

function collectInferredVeoCharacterUsages(
  entries: MarkdownSpecEntry[]
): InferredVeoCharacterUsage[] {
  let order = 0;

  return entries.flatMap((entry) => {
    if (!isVeoMarkdownSpec(entry.content)) {
      return [];
    }

    const clipFilename = extractVeoClipFilename(entry.content, entry.path);
    if (!clipFilename) {
      return [];
    }

    const clipId = clipFilename.replace(/\.[^.]+$/, "");
    const seenCharacterIds = new Set<string>();

    return extractVeoCharacters(entry.content)
      .filter((character) => {
        if (seenCharacterIds.has(character.id)) {
          return false;
        }
        seenCharacterIds.add(character.id);
        return true;
      })
      .map((character) => ({
        sectionId: entry.sectionId,
        path: entry.path,
        clipId,
        characterId: character.id,
        order: order += 1,
      }));
  });
}

export function collectInferredVeoReferences(
  entries: MarkdownSpecEntry[]
): VeoReference[] {
  const byId = new Map<string, VeoReference>();

  entries.forEach((entry) => {
    if (!isVeoMarkdownSpec(entry.content)) {
      return;
    }

    extractVeoCharacters(entry.content).forEach((character) => {
      const existing = byId.get(character.id);
      const mergedSections = uniqueSorted([
        ...(existing?.sections ?? []),
        entry.sectionId,
      ]);
      const prompt = character.prompt ?? existing?.referencePrompt ?? existing?.prompt ?? null;

      byId.set(character.id, {
        ...(existing ?? {}),
        id: character.id,
        label: existing?.label ?? character.label,
        imagePath: existing?.imagePath ?? `outputs/veo/references/${character.id}.png`,
        sections: mergedSections,
        ...(prompt ? { referencePrompt: prompt, prompt } : {}),
        source: "stage6-inferred",
      });
    });
  });

  return Array.from(byId.values()).sort((left, right) => left.id.localeCompare(right.id));
}

export function mergeInferredVeoReferences(
  existing: VeoReference[],
  inferred: VeoReference[]
): VeoReference[] {
  const inferredMap = new Map(inferred.map((reference) => [reference.id, reference]));
  const manualReferences = existing.filter((reference) => reference.source !== "stage6-inferred");

  manualReferences.forEach((reference) => {
    const inferredReference = inferredMap.get(reference.id);
    if (!inferredReference) {
      inferredMap.set(reference.id, reference);
      return;
    }

    inferredMap.set(reference.id, {
      ...inferredReference,
      ...reference,
      sections: uniqueSorted([
        ...inferredReference.sections,
        ...(Array.isArray(reference.sections) ? reference.sections : []),
      ]),
    });
  });

  return Array.from(inferredMap.values()).sort((left, right) => left.id.localeCompare(right.id));
}

export function collectInferredVeoFrameChains(
  entries: MarkdownSpecEntry[]
): VeoFrameChain[] {
  const usages = collectInferredVeoCharacterUsages(entries).sort(
    (left, right) => left.order - right.order
  );
  const primaryReferenceByClip = new Map<string, string>();
  const clipIdsByReference = new Map<string, string[]>();

  for (const usage of usages) {
    if (!primaryReferenceByClip.has(usage.clipId)) {
      primaryReferenceByClip.set(usage.clipId, usage.characterId);
    }

    if (primaryReferenceByClip.get(usage.clipId) !== usage.characterId) {
      continue;
    }

    const clipIds = clipIdsByReference.get(usage.characterId) ?? [];
    if (!clipIds.includes(usage.clipId)) {
      clipIds.push(usage.clipId);
      clipIdsByReference.set(usage.characterId, clipIds);
    }
  }

  return Array.from(clipIdsByReference.entries())
    .filter(([, clips]) => clips.length > 1)
    .map(([referenceId, clips]) => ({
      clips,
      referenceId,
      source: "stage6-inferred",
    }))
    .sort((left, right) => left.referenceId.localeCompare(right.referenceId));
}

export function mergeInferredVeoFrameChains(
  existing: VeoFrameChain[],
  inferred: VeoFrameChain[]
): VeoFrameChain[] {
  const manualChains = existing.filter((chain) => chain.source !== "stage6-inferred");
  const manualReferenceIds = new Set(
    manualChains.map((chain) => chain.referenceId).filter((referenceId) => typeof referenceId === "string")
  );

  return [...inferred.filter((chain) => !manualReferenceIds.has(chain.referenceId)), ...manualChains].sort(
    (left, right) => left.referenceId.localeCompare(right.referenceId)
  );
}

function listProjectVeoSpecEntries(
  projectDir: string,
  sections: Section[]
): MarkdownSpecEntry[] {
  return sections.flatMap((section) => {
    const normalizedSpecDir = normalizeSpecDir(section.specDir ?? section.id);
    const specDir = path.join(projectDir, "specs", normalizedSpecDir);
    if (!fs.existsSync(specDir)) {
      return [];
    }

    return fs
      .readdirSync(specDir)
      .filter((file) => file.endsWith(".md") && !file.startsWith("AUDIT_"))
      .sort((left, right) => left.localeCompare(right))
      .map((file) => ({
        sectionId: section.id,
        path: path.posix.join("specs", normalizedSpecDir, file),
        content: fs.readFileSync(path.join(specDir, file), "utf-8"),
      }));
  });
}

export function syncInferredVeoReferencesFromProjectSpecs(
  projectDir: string,
  config: ProjectConfig
): ProjectConfig {
  const specEntries = listProjectVeoSpecEntries(projectDir, config.sections);
  const inferredReferences = collectInferredVeoReferences(specEntries);
  const inferredFrameChains = collectInferredVeoFrameChains(specEntries);
  const mergedReferences = mergeInferredVeoReferences(
    config.veo.references ?? [],
    inferredReferences
  );
  const mergedFrameChains = mergeInferredVeoFrameChains(
    config.veo.frameChains ?? [],
    inferredFrameChains
  );

  return {
    ...config,
    veo: {
      ...config.veo,
      references: mergedReferences,
      frameChains: mergedFrameChains,
    },
  };
}
