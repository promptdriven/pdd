import { parseSpecTimestampRange } from "./spec-timestamp";

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

export function parseSpecTimingWindow(specContent: string): SpecTimingWindow | null {
  const range = parseSpecTimestampRange(specContent);
  if (!range) {
    return null;
  }

  return range;
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
