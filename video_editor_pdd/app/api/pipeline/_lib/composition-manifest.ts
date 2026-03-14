import fs from "fs";
import path from "path";

import { getProjectDir } from "@/lib/projects";
import type { Section } from "@/lib/types";

type SectionCompositionEntry = NonNullable<Section["compositions"]>[number];

export type GeneratedCompositionManifestSection = {
  id: string;
  compositionId: string;
  specDir?: string;
  timelineSource?: string;
  compositions: SectionCompositionEntry[];
};

type GeneratedCompositionManifest = {
  version: 1;
  updatedAt: string;
  sections: GeneratedCompositionManifestSection[];
};

export function getCompositionManifestPath(projectDir = getProjectDir()): string {
  return path.join(projectDir, "outputs", "compositions", "manifest.json");
}

export function loadCompositionManifest(
  projectDir = getProjectDir()
): GeneratedCompositionManifest | null {
  const manifestPath = getCompositionManifestPath(projectDir);
  if (!fs.existsSync(manifestPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(fs.readFileSync(manifestPath, "utf-8")) as
      | GeneratedCompositionManifest
      | null;
    if (
      !parsed ||
      !Array.isArray(parsed.sections) ||
      typeof parsed.updatedAt !== "string"
    ) {
      return null;
    }

    return parsed;
  } catch {
    return null;
  }
}

export function mergeCompositionManifest(
  sections: GeneratedCompositionManifestSection[],
  projectDir = getProjectDir()
): void {
  const existing = loadCompositionManifest(projectDir);
  const mergedById = new Map<string, GeneratedCompositionManifestSection>();

  for (const section of existing?.sections ?? []) {
    mergedById.set(section.id, section);
  }

  for (const section of sections) {
    mergedById.set(section.id, section);
  }

  const manifest: GeneratedCompositionManifest = {
    version: 1,
    updatedAt: new Date().toISOString(),
    sections: Array.from(mergedById.values()),
  };

  const manifestPath = getCompositionManifestPath(projectDir);
  fs.mkdirSync(path.dirname(manifestPath), { recursive: true });
  fs.writeFileSync(manifestPath, JSON.stringify(manifest, null, 2), "utf-8");
}

export function resolveSectionGeneratedMetadata(
  section: Pick<Section, "id">
): GeneratedCompositionManifestSection | null {
  return (
    loadCompositionManifest()?.sections.find(
      (candidate) => candidate.id === section.id
    ) ?? null
  );
}

export function resolveSectionCompositionEntries(
  section: Pick<Section, "id" | "compositions">
): SectionCompositionEntry[] {
  const fromManifest = resolveSectionGeneratedMetadata(section)?.compositions;
  if (Array.isArray(fromManifest) && fromManifest.length > 0) {
    return fromManifest;
  }

  return section.compositions ?? [];
}

export function resolveSectionCompositionIds(
  section: Pick<Section, "id" | "compositions">
): string[] {
  return resolveSectionCompositionEntries(section)
    .map((composition) =>
      typeof composition === "string" ? composition : composition?.id
    )
    .filter((compositionId): compositionId is string => Boolean(compositionId));
}
