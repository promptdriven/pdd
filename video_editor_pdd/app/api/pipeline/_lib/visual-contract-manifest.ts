import fs from "fs";
import path from "path";

import { getProjectDir } from "@/lib/projects";

export type GeneratedTimingAnchor =
  | {
      type: "segmentStart" | "segmentEnd";
      segmentId: string;
      offsetMs?: number;
    }
  | {
      type: "absolute";
      seconds: number;
    }
  | {
      type: "sectionStart" | "sectionEnd";
      offsetMs?: number;
    };

export type GeneratedVisualContract = {
  id: string;
  specBaseName: string;
  specPath?: string | null;
  dataPoints?: unknown;
  mediaAliases?: Record<string, string>;
  overlayConfig?: Record<string, unknown> | null;
  renderMode?: "raw-media" | "generated-media" | "component";
  coverSegments?: string[];
  parentId?: string;
  children?: string[];
  laneHint?: "main" | "overlay" | "background" | number;
  startAnchor?: GeneratedTimingAnchor;
  endAnchor?: GeneratedTimingAnchor;
  startOffsetMs?: number;
  endOffsetMs?: number;
};

type GeneratedVisualContractSection = {
  id: string;
  visuals: GeneratedVisualContract[];
};

type GeneratedVisualContractManifest = {
  version: 1;
  updatedAt: string;
  sections: GeneratedVisualContractSection[];
};

export function getVisualContractManifestPath(projectDir = getProjectDir()): string {
  return path.join(projectDir, "outputs", "compositions", "visual-manifest.json");
}

export function loadVisualContractManifest(
  projectDir = getProjectDir()
): GeneratedVisualContractManifest | null {
  const manifestPath = getVisualContractManifestPath(projectDir);
  if (!fs.existsSync(manifestPath)) {
    return null;
  }

  try {
    const parsed = JSON.parse(
      fs.readFileSync(manifestPath, "utf-8")
    ) as GeneratedVisualContractManifest | null;
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

export function resolveSectionVisualContract(
  sectionId: string,
  visualIdOrSpecBaseName: string,
  projectDir = getProjectDir()
): GeneratedVisualContract | null {
  const section = loadVisualContractManifest(projectDir)?.sections.find(
    (candidate) => candidate.id === sectionId
  );
  if (!section) {
    return null;
  }

  return (
    section.visuals.find(
      (visual) =>
        visual.id === visualIdOrSpecBaseName ||
        visual.specBaseName === visualIdOrSpecBaseName
    ) ?? null
  );
}
