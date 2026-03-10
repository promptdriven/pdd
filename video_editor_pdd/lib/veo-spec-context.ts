export type VeoMarkdownSpecSelection = {
  path: string;
};

export type ResolvedVeoClipSpec = {
  id: string;
  path: string;
  prompt: string;
  filename: string;
  chainFromPrevious: boolean;
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

function extractJsonBooleanField(
  content: string,
  fieldNames: string[]
): boolean | null {
  for (const fieldName of fieldNames) {
    const match = content.match(
      new RegExp(`"${fieldName}"\\s*:\\s*(true|false)`, "i")
    );
    if (!match) {
      continue;
    }

    return match[1].toLowerCase() === "true";
  }

  return null;
}

export function extractVeoPrompt(content: string): string | null {
  return (
    extractVeoMarker(content) ??
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
  return null;
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
      const chainFromPrevious =
        extractJsonBooleanField(entry.content, [
          "chainFromPrevious",
          "referenceFromPrevious",
        ]) ?? false;
      return {
        id,
        path: entry.path,
        prompt,
        filename,
        chainFromPrevious,
      };
    })
    .filter((entry): entry is ResolvedVeoClipSpec => entry !== null);
}
