export type VeoMarkdownSpecSelection = {
  path: string;
};

export type ResolvedVeoClipSpec = {
  id: string;
  path: string;
  prompt: string;
  filename: string;
};

type MarkdownSpecEntry = {
  path: string;
  content: string;
};

const JSON_STRING_FIELD_RE = (
  fieldNames: string[]
): RegExp =>
  new RegExp(
    `"(${fieldNames.join("|")})"\\s*:\\s*"([^"\\\\]*(?:\\\\.[^"\\\\]*)*)"`,
    "i"
  );

export function normalizeSpecDir(value: string): string {
  return value
    .replace(/\\/g, "/")
    .replace(/^\.?\//, "")
    .replace(/^specs\//, "")
    .replace(/\/+$/, "");
}

export function extractVeoMarker(content: string): string | null {
  const match = content.match(/\[veo:\s*([^\]]+?)\]/i);
  const prompt = match?.[1]?.trim();
  return prompt ? prompt : null;
}

function stripOptionalCodeFence(content: string): string {
  const trimmed = content.trim();
  if (!trimmed.startsWith("```")) {
    return trimmed;
  }

  const lines = trimmed.split(/\r?\n/);
  if (lines.length === 0) {
    return trimmed;
  }

  const withoutOpenFence = lines.slice(1);
  const closingFenceIndex = withoutOpenFence.findIndex((line) => line.trim() === "```");
  const bodyLines =
    closingFenceIndex >= 0
      ? withoutOpenFence.slice(0, closingFenceIndex)
      : withoutOpenFence;

  return bodyLines.join("\n").trim();
}

export function extractMarkdownJsonBlock(
  content: string,
  heading: string
): Record<string, unknown> | null {
  const escapedHeading = heading.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const headingPattern =
    heading.trim().toLowerCase() === "data points"
      ? `${escapedHeading}(?:\\s+JSON)?`
      : escapedHeading;
  const match = content.match(
    new RegExp(
      `(?:^|\\n)#{2,6}\\s+${headingPattern}\\s*\\n\\\`\\\`\\\`json\\s*([\\s\\S]*?)\\\`\\\`\\\``,
      "i"
    )
  );
  const rawJson = match?.[1]?.trim();
  if (!rawJson) {
    return null;
  }

  try {
    const parsed = JSON.parse(rawJson);
    return parsed && typeof parsed === "object" && !Array.isArray(parsed)
      ? (parsed as Record<string, unknown>)
      : null;
  } catch {
    return null;
  }
}

function extractVeoPromptSection(content: string): string | null {
  const match = content.match(
    /(?:^|\n)#{2,6}\s+Veo Prompt\s*\n([\s\S]*?)(?=\n#{1,6}\s|\n---\s*$|$)/i
  );
  const rawSectionBody = match?.[1]?.trim();
  if (!rawSectionBody) {
    return null;
  }

  const prompt = stripOptionalCodeFence(rawSectionBody);
  return prompt || null;
}

function extractJsonStringField(
  content: string,
  fieldNames: string[]
): string | null {
  const match = content.match(JSON_STRING_FIELD_RE(fieldNames));
  const rawValue = match?.[2];
  if (!rawValue) {
    return null;
  }

  try {
    return JSON.parse(`"${rawValue}"`);
  } catch {
    return rawValue;
  }
}

export function extractVeoPrompt(content: string): string | null {
  return (
    extractVeoMarker(content) ??
    extractVeoPromptSection(content) ??
    extractJsonStringField(content, ["veoPrompt", "prompt", "videoPrompt"])
  );
}

export function extractVeoClipFilename(content: string, _specPath: string): string | null {
  const clipSource =
    extractJsonStringField(content, ["clipSource", "outputSrc", "filename"]) ??
    null;

  if (clipSource) {
    const normalized = clipSource.replace(/\\/g, "/");
    const basename = normalized.split("/").pop() ?? normalized;
    return basename || null;
  }

  const clipId =
    extractJsonStringField(content, ["clip_id", "clipId"]) ?? null;

  if (clipId) {
    const normalized = clipId.replace(/\\/g, "/");
    const basename = normalized.split("/").pop() ?? normalized;
    if (!basename) {
      return null;
    }

    return /\.[^.]+$/.test(basename) ? basename : `${basename}.mp4`;
  }

  const fallbackBaseName = _specPath
    .replace(/\\/g, "/")
    .split("/")
    .pop()
    ?.replace(/\.[^.]+$/, "");

  return fallbackBaseName ? `${fallbackBaseName}.mp4` : null;
}

export function isVeoMarkdownSpec(content: string): boolean {
  return /^\s*\[veo:[^\]]*\]/i.test(content) || /\*\*Tool:\*\*\s*Veo\b/i.test(content);
}

export function selectCanonicalVeoMarkdownSpec(
  entries: MarkdownSpecEntry[]
): VeoMarkdownSpecSelection | null {
  const sortedEntries = [...entries].sort((left, right) => left.path.localeCompare(right.path));

  for (const entry of sortedEntries) {
    if (isVeoMarkdownSpec(entry.content)) {
      return {
        path: entry.path,
      };
    }
  }

  return null;
}

export function selectCanonicalVeoPromptSpec(
  entries: MarkdownSpecEntry[]
): { path: string; prompt: string } | null {
  const sortedEntries = [...entries].sort((left, right) => left.path.localeCompare(right.path));

  for (const entry of sortedEntries) {
    const prompt = extractVeoPrompt(entry.content);
    if (prompt) {
      return {
        path: entry.path,
        prompt,
      };
    }
  }

  return null;
}

export function listResolvedVeoClipSpecs(
  entries: MarkdownSpecEntry[]
): ResolvedVeoClipSpec[] {
  return [...entries]
    .sort((left, right) => left.path.localeCompare(right.path))
    .filter((entry) => isVeoMarkdownSpec(entry.content))
    .map((entry) => {
      const prompt = extractVeoPrompt(entry.content);
      const filename = extractVeoClipFilename(entry.content, entry.path);

      if (!prompt || !filename) {
        return null;
      }

      const id = filename.replace(/\.[^.]+$/, "");
      return {
        id,
        path: entry.path,
        prompt,
        filename,
      };
    })
    .filter((entry): entry is ResolvedVeoClipSpec => entry !== null);
}
