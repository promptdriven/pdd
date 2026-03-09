export type SpecTimingWindow = {
  startSeconds: number;
  endSeconds: number;
};

export type SpecTimingWord = {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
};

function parseClockTime(value: string): number | null {
  const trimmed = value.trim();
  if (!trimmed) {
    return null;
  }

  const parts = trimmed.split(":").map((part) => Number(part));
  if (parts.some((part) => Number.isNaN(part))) {
    return null;
  }

  if (parts.length === 1) {
    return parts[0] ?? null;
  }

  if (parts.length === 2) {
    return (parts[0] ?? 0) * 60 + (parts[1] ?? 0);
  }

  if (parts.length === 3) {
    return (parts[0] ?? 0) * 3600 + (parts[1] ?? 0) * 60 + (parts[2] ?? 0);
  }

  return null;
}

export function parseSpecTimingWindow(specContent: string): SpecTimingWindow | null {
  const match = specContent.match(
    /\*\*Timestamp:\*\*\s*([0-9:.]+)\s*-\s*([0-9:.]+)/i
  );
  if (!match) {
    return null;
  }

  const startSeconds = parseClockTime(match[1] ?? "");
  const endSeconds = parseClockTime(match[2] ?? "");

  if (
    startSeconds === null ||
    endSeconds === null ||
    endSeconds <= startSeconds
  ) {
    return null;
  }

  return { startSeconds, endSeconds };
}

export function filterWordsForSpecTimingWindow(
  words: SpecTimingWord[],
  window: SpecTimingWindow | null
): SpecTimingWord[] {
  if (!window) {
    return words;
  }

  return words.filter((word) => {
    return word.end > window.startSeconds && word.start < window.endSeconds;
  });
}
