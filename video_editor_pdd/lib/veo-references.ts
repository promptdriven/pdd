import fs from "fs";
import path from "path";

import type { ProjectConfig, Section, VeoReference } from "./types";
import { extractMarkdownJsonBlock, isVeoMarkdownSpec, normalizeSpecDir } from "./veo-spec-context";

type MarkdownSpecEntry = {
  sectionId: string;
  path: string;
  content: string;
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
  const inferredReferences = collectInferredVeoReferences(
    listProjectVeoSpecEntries(projectDir, config.sections)
  );
  const mergedReferences = mergeInferredVeoReferences(
    config.veo.references ?? [],
    inferredReferences
  );

  return {
    ...config,
    veo: {
      ...config.veo,
      references: mergedReferences,
    },
  };
}
