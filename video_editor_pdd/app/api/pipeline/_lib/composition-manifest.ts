import fs from "fs";
import path from "path";
import { createHash } from "crypto";

import { getAppScriptsDir, getAppRemotionSrcDir, getProjectDir } from "@/lib/projects";
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
  generatorFingerprint?: string;
  sections: GeneratedCompositionManifestSection[];
};

type CompositionArtifactState = {
  stale: boolean;
  manifestFingerprint: string | null;
  currentFingerprint: string;
  reason: "generator_changed" | "missing_manifest_fingerprint" | null;
};

const COMPOSITION_GENERATOR_FINGERPRINT_VERSION = 1;

function getCompositionGeneratorInputPaths(): string[] {
  return [
    path.join(getAppScriptsDir(), "generate_section_compositions.py"),
    path.join(process.cwd(), "lib", "composition-timing.ts"),
    path.join(process.cwd(), "lib", "spec-timestamp.ts"),
    path.join(process.cwd(), "lib", "section-timing.ts"),
    path.join(process.cwd(), "lib", "section-timeline.ts"),
    path.join(process.cwd(), "lib", "narration-manifest.ts"),
    path.join(
      process.cwd(),
      "app",
      "api",
      "pipeline",
      "_lib",
      "visual-contract-manifest.ts"
    ),
    path.join(getAppRemotionSrcDir(), "_shared", "visual-runtime.tsx"),
  ];
}

export function getCompositionGeneratorFingerprint(): string {
  const hash = createHash("sha256");
  hash.update(`composition-generator-v${COMPOSITION_GENERATOR_FINGERPRINT_VERSION}`);

  for (const inputPath of getCompositionGeneratorInputPaths()) {
    if (!fs.existsSync(inputPath)) {
      continue;
    }

    hash.update(path.relative(process.cwd(), inputPath));
    hash.update(fs.readFileSync(inputPath));
  }

  return hash.digest("hex");
}

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
    generatorFingerprint: getCompositionGeneratorFingerprint(),
    sections: Array.from(mergedById.values()),
  };

  const manifestPath = getCompositionManifestPath(projectDir);
  fs.mkdirSync(path.dirname(manifestPath), { recursive: true });
  fs.writeFileSync(manifestPath, JSON.stringify(manifest, null, 2), "utf-8");
}

export function getCompositionArtifactState(
  projectDir = getProjectDir()
): CompositionArtifactState {
  const manifest = loadCompositionManifest(projectDir);
  const currentFingerprint = getCompositionGeneratorFingerprint();

  if (!manifest) {
    return {
      stale: false,
      manifestFingerprint: null,
      currentFingerprint,
      reason: null,
    };
  }

  const manifestFingerprint =
    typeof manifest.generatorFingerprint === "string" &&
    manifest.generatorFingerprint.trim().length > 0
      ? manifest.generatorFingerprint
      : null;

  if (!manifestFingerprint) {
    return {
      stale: true,
      manifestFingerprint: null,
      currentFingerprint,
      reason: "missing_manifest_fingerprint",
    };
  }

  const stale = manifestFingerprint !== currentFingerprint;
  return {
    stale,
    manifestFingerprint,
    currentFingerprint,
    reason: stale ? "generator_changed" : null,
  };
}

export function isCompositionArtifactSetStale(
  projectDir = getProjectDir()
): boolean {
  return getCompositionArtifactState(projectDir).stale;
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
