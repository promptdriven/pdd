import type { OutputResolution } from "@/lib/types";

type Dimensions = {
  width: number;
  height: number;
};

const ANNOTATION_UPDATE_BLOCK_RE =
  /<!--\s*ANNOTATION_UPDATE_START:[\s\S]*?<!--\s*ANNOTATION_UPDATE_END:[\s\S]*?-->\s*/gi;
function roundScaled(value: number): string {
  return Number.isInteger(value) ? String(value) : value.toFixed(2).replace(/\.?0+$/, "");
}

export function detectSpecResolution(specContent: string): Dimensions | null {
  const match = specContent.match(/Resolution:\s*(\d+)\s*x\s*(\d+)/i);
  if (!match) {
    return null;
  }

  return {
    width: Number(match[1]),
    height: Number(match[2]),
  };
}

function scaleCoordinate(value: string, factor: number): string {
  return roundScaled(Number(value) * factor);
}

export function normalizeSpecForAudit(
  specContent: string,
  targetResolution: OutputResolution
): string {
  const sanitizedContent = specContent.replace(ANNOTATION_UPDATE_BLOCK_RE, "").trim();
  const sourceResolution = detectSpecResolution(sanitizedContent);
  if (!sourceResolution) {
    return sanitizedContent;
  }

  if (
    sourceResolution.width === targetResolution.width &&
    sourceResolution.height === targetResolution.height
  ) {
    return sanitizedContent;
  }

  const scaleX = targetResolution.width / sourceResolution.width;
  const scaleY = targetResolution.height / sourceResolution.height;

  let normalized = sanitizedContent.replace(
    /Resolution:\s*\d+\s*x\s*\d+/gi,
    `Resolution: ${targetResolution.width}x${targetResolution.height}`
  );

  normalized = normalized.replace(
    /\(\s*(\d+(?:\.\d+)?)\s*,\s*(\d+(?:\.\d+)?)\s*\)/g,
    (_, x, y) => `(${scaleCoordinate(x, scaleX)}, ${scaleCoordinate(y, scaleY)})`
  );

  normalized = normalized.replace(
    /\bx\s*=\s*(\d+(?:\.\d+)?)/gi,
    (_, x) => `x=${scaleCoordinate(x, scaleX)}`
  );

  normalized = normalized.replace(
    /\by\s*=\s*(\d+(?:\.\d+)?)/gi,
    (_, y) => `y=${scaleCoordinate(y, scaleY)}`
  );

  normalized = normalized.replace(
    /(\d+(?:\.\d+)?)px/g,
    (full, value) => {
      const numeric = Number(value);
      const factor =
        Math.abs(numeric - sourceResolution.width) <= Math.abs(numeric - sourceResolution.height)
          ? scaleX
          : scaleY;
      return `${scaleCoordinate(value, factor)}px`;
    }
  );

  normalized = normalized.replace(
    new RegExp(`\\b${sourceResolution.width}\\s*x\\s*${sourceResolution.height}\\b`, "g"),
    `${targetResolution.width}x${targetResolution.height}`
  );

  return normalized;
}

export function buildClaudeAuditSpecSnapshot(
  specContent: string,
  targetResolution: OutputResolution
): string {
  const normalized = normalizeSpecForAudit(specContent, targetResolution);
  const strippedForClaude = normalized
    .split(/\n(?=##\s+)/)
    .filter((section) => !/^##\s*(Code Structure|Data Points)\b/i.test(section.trim()))
    .join("\n")
    .trim();

  let relativized = strippedForClaude.replace(
    /\bcentered\s+at\s*\(\s*\d+(?:\.\d+)?\s*,\s*\d+(?:\.\d+)?\s*\)/gi,
    "visually centered on the canvas"
  );

  relativized = relativized.replace(
    /\b(\d+(?:\.\d+)?)px\s+width\b/gi,
    (_full, value) =>
      Number(value) === targetResolution.width ? "full frame width" : "intended visual width"
  );

  relativized = relativized.replace(
    /\bx\s*=\s*\d+(?:\.\d+)?/gi,
    "expected horizontal anchor"
  );

  relativized = relativized.replace(
    /\by\s*=\s*\d+(?:\.\d+)?/gi,
    "expected vertical anchor"
  );

  relativized = relativized.replace(
    /\(\s*\d+(?:\.\d+)?\s*,\s*\d+(?:\.\d+)?\s*\)/g,
    "(intended anchor position)"
  );

  return relativized;
}
