import fs from "fs";
import path from "path";

import type { VeoConfig, VeoReference } from "@/lib/types";

export type VeoChainPlan = {
  previousClipId: string | null;
  referenceImagePath: string | null;
  needsLastFrame: boolean;
};

export const resolveReferenceImagePath = (
  projectDir: string,
  references: VeoReference[],
  referenceId: string
): string | null => {
  const generatedPath = path.join(
    projectDir,
    "outputs",
    "veo",
    "references",
    `${referenceId}.png`
  );

  if (fs.existsSync(generatedPath)) {
    return generatedPath;
  }

  const reference = references.find((entry) => entry.id === referenceId);
  if (!reference?.imagePath) {
    return null;
  }

  const configuredPath = path.isAbsolute(reference.imagePath)
    ? reference.imagePath
    : path.join(projectDir, reference.imagePath);

  return fs.existsSync(configuredPath) ? configuredPath : null;
};

const defaultPlan = (): VeoChainPlan => ({
  previousClipId: null,
  referenceImagePath: null,
  needsLastFrame: false,
});

export const resolveVeoFrameChainPlan = (
  projectDir: string,
  clipIds: string[],
  veoConfig?: Partial<VeoConfig> | null
): Map<string, VeoChainPlan> => {
  const plan = new Map<string, VeoChainPlan>();
  const clipIdSet = new Set(clipIds);
  const references = veoConfig?.references ?? [];
  const frameChains = veoConfig?.frameChains ?? [];
  const assignedClipIds = new Set<string>();

  for (const clipId of clipIds) {
    plan.set(clipId, defaultPlan());
  }

  for (const chain of frameChains) {
    const chainClips = (chain?.clips ?? []).filter((clipId) => clipIdSet.has(clipId));
    if (chainClips.length === 0) {
      continue;
    }

    const usePreviousFrames = chain.chainFromPrevious !== false;
    const initialReferencePath = chain.referenceId
      ? resolveReferenceImagePath(projectDir, references, chain.referenceId)
      : null;

    for (let index = 0; index < chainClips.length; index += 1) {
      const clipId = chainClips[index];
      if (!clipId || assignedClipIds.has(clipId)) {
        continue;
      }

      const previousClipId =
        usePreviousFrames && index > 0 ? chainClips[index - 1] ?? null : null;
      const needsLastFrame =
        usePreviousFrames && index < chainClips.length - 1;

      plan.set(clipId, {
        previousClipId,
        referenceImagePath: previousClipId ? null : initialReferencePath,
        needsLastFrame,
      });
      assignedClipIds.add(clipId);
    }
  }

  return plan;
};
