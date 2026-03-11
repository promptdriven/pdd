import fs from "fs";
import path from "path";

import { listSectionVisualIds, resolveSectionVisualTimings } from "./composition-timing";
import type { Annotation, Section } from "./types";
import { listResolvedVeoClipSpecs, normalizeSpecDir } from "./veo-spec-context";

type SectionTarget = Pick<
  Section,
  "id" | "label" | "specDir" | "durationSeconds" | "offsetSeconds" | "compositionId" | "compositions"
>;

export type VeoPromptPatchResult = {
  clipId: string;
  specPath: string;
  prompt: string;
};

const QUOTED_PROMPT_RE =
  /update\s+the\s+veo\s+prompt\s+to:\s*(?:"([^"]+)"|'([^']+)'|`([^`]+)`)/i;
const REPLACEMENT_PROMPT_RE =
  /update\s+the\s+veo\s+prompt\s+from\s+(?:"[^"]+"|'[^']+'|`[^`]+`)\s+to\s+(?:"([^"]+)"|'([^']+)'|`([^`]+)`)/i;
const EXAMPLE_PROMPT_RE =
  /update\s+the\s+veo\s+prompt[\s\S]*?(?:e\.g\.:|for example:)\s*(?:"([^"]+)"|'([^']+)'|`([^`]+)`)/i;
const SPEC_TARGET_RE = /\b(\d{2}_[a-z0-9_]+)(?:\.md)?\b/i;
const CLIP_TARGET_RE = /\b(?:veo\/)?([a-z0-9_]+)\.mp4\b/i;

function loadSectionMarkdownEntries(projectDir: string, section: SectionTarget) {
  const specDir = path.join(
    projectDir,
    "specs",
    normalizeSpecDir(section.specDir ?? section.id)
  );

  if (!fs.existsSync(specDir)) {
    return [];
  }

  return fs
    .readdirSync(specDir)
    .filter((file) => file.endsWith(".md") && !file.startsWith("AUDIT_"))
    .map((file) => ({
      path: path.posix.join("specs", normalizeSpecDir(section.specDir ?? section.id), file),
      content: fs.readFileSync(path.join(specDir, file), "utf-8"),
    }));
}

export function extractSuggestedVeoPrompt(
  annotation: Pick<Annotation, "analysis" | "text">
): string | null {
  const suggestedFixes = annotation.analysis?.suggestedFixes ?? [];

  for (const suggestedFix of suggestedFixes) {
    const replacementMatch = suggestedFix.match(REPLACEMENT_PROMPT_RE);
    const replacementPrompt =
      replacementMatch?.[1] ?? replacementMatch?.[2] ?? replacementMatch?.[3];
    if (replacementPrompt?.trim()) {
      return replacementPrompt.trim();
    }

    const match = suggestedFix.match(QUOTED_PROMPT_RE);
    const prompt = match?.[1] ?? match?.[2] ?? match?.[3];
    if (prompt?.trim()) {
      return prompt.trim();
    }

    const exampleMatch = suggestedFix.match(EXAMPLE_PROMPT_RE);
    const examplePrompt =
      exampleMatch?.[1] ?? exampleMatch?.[2] ?? exampleMatch?.[3];
    if (examplePrompt?.trim()) {
      return examplePrompt.trim();
    }
  }

  return null;
}

function normalizeExplicitTarget(value: string): string {
  return value.trim().toLowerCase().replace(/\.md$/i, "").replace(/\.mp4$/i, "");
}

function extractExplicitVeoTarget(
  annotation: Pick<Annotation, "analysis" | "text">
): string | null {
  const candidateTexts = [
    annotation.analysis?.technicalAssessment ?? "",
    ...(annotation.analysis?.suggestedFixes ?? []),
    annotation.text ?? "",
  ];

  for (const candidateText of candidateTexts) {
    const clipMatch = candidateText.match(CLIP_TARGET_RE);
    const clipTarget = clipMatch?.[1];
    if (clipTarget) {
      return normalizeExplicitTarget(clipTarget);
    }

    const specMatch = candidateText.match(SPEC_TARGET_RE);
    const specTarget = specMatch?.[1];
    if (specTarget) {
      return normalizeExplicitTarget(specTarget);
    }
  }

  return null;
}

function replaceVeoMarker(content: string, prompt: string): string {
  const marker = `[veo: ${prompt}]`;
  if (/^\s*\[veo:[^\]]*\]/i.test(content)) {
    return content.replace(/^\s*\[veo:[^\]]*\]/i, marker);
  }

  if (/^\s*\[veo:\s*\]/i.test(content)) {
    return content.replace(/^\s*\[veo:\s*\]/i, marker);
  }

  return `${marker}\n\n${content}`;
}

function replaceVeoPromptJsonField(content: string, prompt: string): string {
  const quotedPrompt = JSON.stringify(prompt);
  if (/"veoPrompt"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"/i.test(content)) {
    return content.replace(
      /"veoPrompt"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"/i,
      `"veoPrompt": ${quotedPrompt}`
    );
  }

  if (/"prompt"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"/i.test(content)) {
    return content.replace(
      /"prompt"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"/i,
      `"prompt": ${quotedPrompt}`
    );
  }

  if (/"videoPrompt"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"/i.test(content)) {
    return content.replace(
      /"videoPrompt"\s*:\s*"([^"\\]*(?:\\.[^"\\]*)*)"/i,
      `"videoPrompt": ${quotedPrompt}`
    );
  }

  return content;
}

function resolveTargetVeoSpec(
  projectDir: string,
  section: SectionTarget,
  annotation: Pick<Annotation, "analysis" | "text" | "timestamp">
): { clipId: string; specPath: string } | null {
  const markdownEntries = loadSectionMarkdownEntries(projectDir, section);
  const resolvedClips = listResolvedVeoClipSpecs(markdownEntries);
  if (resolvedClips.length === 0) {
    return null;
  }

  const visualIds = listSectionVisualIds(projectDir, section, []);
  const timings = resolveSectionVisualTimings(projectDir, section, visualIds);

  const candidates = resolvedClips
    .map((clip) => {
      const absoluteSpecPath = path.join(projectDir, clip.path);
      const timing = timings.find((candidate) => {
        if (candidate.specPath && path.resolve(candidate.specPath) === path.resolve(absoluteSpecPath)) {
          return true;
        }

        return candidate.id === clip.id;
      });

      return {
        clipId: clip.id,
        specPath: absoluteSpecPath,
        startSeconds: timing?.startSeconds ?? 0,
        endSeconds: timing?.endSeconds ?? 0,
      };
    })
    .sort((left, right) => left.startSeconds - right.startSeconds);

  const explicitTarget = extractExplicitVeoTarget(annotation);
  if (explicitTarget) {
    const explicitMatch = candidates.find((candidate) => {
      const specBaseName = path.basename(candidate.specPath, path.extname(candidate.specPath)).toLowerCase();
      return (
        candidate.clipId.toLowerCase() === explicitTarget ||
        specBaseName === explicitTarget
      );
    });

    if (explicitMatch) {
      return {
        clipId: explicitMatch.clipId,
        specPath: explicitMatch.specPath,
      };
    }
  }

  if (annotation.timestamp != null) {
    const annotationTimestamp = annotation.timestamp;
    const directMatch = candidates.find(
      (candidate) =>
        annotationTimestamp >= candidate.startSeconds &&
        annotationTimestamp < candidate.endSeconds
    );
    if (directMatch) {
      return {
        clipId: directMatch.clipId,
        specPath: directMatch.specPath,
      };
    }

    const nearest = candidates.reduce((best, candidate) => {
      const candidateDistance = Math.abs(
        annotationTimestamp - (candidate.startSeconds + candidate.endSeconds) / 2
      );
      const bestDistance = Math.abs(
        annotationTimestamp - (best.startSeconds + best.endSeconds) / 2
      );
      return candidateDistance < bestDistance ? candidate : best;
    });

    return {
      clipId: nearest.clipId,
      specPath: nearest.specPath,
    };
  }

  return {
    clipId: candidates[0].clipId,
    specPath: candidates[0].specPath,
  };
}

export function applyVeoPromptFixForAnnotation(
  projectDir: string,
  section: SectionTarget,
  annotation: Pick<Annotation, "analysis" | "text" | "timestamp">
): VeoPromptPatchResult | null {
  const prompt = extractSuggestedVeoPrompt(annotation);
  if (!prompt) {
    return null;
  }

  const target = resolveTargetVeoSpec(projectDir, section, annotation);
  if (!target) {
    return null;
  }

  const currentContent = fs.readFileSync(target.specPath, "utf-8");
  let updatedContent = replaceVeoMarker(currentContent, prompt);
  updatedContent = replaceVeoPromptJsonField(updatedContent, prompt);

  if (updatedContent !== currentContent) {
    fs.writeFileSync(target.specPath, updatedContent);
  }

  return {
    clipId: target.clipId,
    specPath: target.specPath,
    prompt,
  };
}
