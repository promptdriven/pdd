export type VeoMarkdownSpecSelection = {
  path: string;
};

type MarkdownSpecEntry = {
  path: string;
  content: string;
};

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
    const prompt = extractVeoMarker(entry.content);
    if (prompt) {
      return {
        path: entry.path,
        prompt,
      };
    }
  }

  return null;
}
