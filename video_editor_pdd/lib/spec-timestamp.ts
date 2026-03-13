const TIMESTAMP_SEPARATOR_RE = "[-–—]";
const MIN_SECTION_GUARD_SECONDS = 1 / 30;

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

export function parseSpecTimestampRange(content: string): {
  startSeconds: number;
  endSeconds: number;
} | null {
  const match = content.match(
    new RegExp(
      `\\*\\*Timestamp:\\*\\*\\s*([0-9:.]+)\\s*${TIMESTAMP_SEPARATOR_RE}\\s*([0-9:.]+)`,
      "i"
    )
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

export function normalizeSpecTimestampRangeToSection(
  range: { startSeconds: number; endSeconds: number },
  sectionDurationSeconds: number,
  sectionOffsetSeconds = 0,
  minSectionGuardSeconds = MIN_SECTION_GUARD_SECONDS
): { startSeconds: number; endSeconds: number } {
  if (sectionOffsetSeconds <= 0) {
    return range;
  }

  const fitsSectionWindow =
    range.startSeconds >= 0 &&
    range.endSeconds <= sectionDurationSeconds + minSectionGuardSeconds;
  const shifted = {
    startSeconds: range.startSeconds - sectionOffsetSeconds,
    endSeconds: range.endSeconds - sectionOffsetSeconds,
  };
  const shiftedFitsSectionWindow =
    shifted.endSeconds > 0 &&
    shifted.startSeconds < sectionDurationSeconds + minSectionGuardSeconds;

  return !fitsSectionWindow && shiftedFitsSectionWindow ? shifted : range;
}
