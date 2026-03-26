export interface SegmentValidationLike {
  segmentId: string;
  matchRatio: number | null;
  status: "pass" | "warn" | "fail" | "skip";
}

export interface RunFlaggedTranscriptRerenderRetriesOptions<T extends SegmentValidationLike> {
  initialRows: T[];
  thresholdPercent: number;
  maxRetries: number;
  sectionId: string;
  startTtsRerender: (segmentIds: string[]) => Promise<string>;
  startAudioSync: (sectionId: string) => Promise<string>;
  waitForJob: (jobId: string) => Promise<void>;
  reloadValidationRows: () => Promise<T[]>;
  onTtsJobStarted?: (info: {
    attempt: number;
    jobId: string;
    segmentIds: string[];
  }) => void;
  onAudioSyncJobStarted?: (info: {
    attempt: number;
    jobId: string;
    sectionId: string;
  }) => void;
}

export interface RunFlaggedTranscriptRerenderRetriesResult<T extends SegmentValidationLike> {
  attemptsCompleted: number;
  finalRows: T[];
  remainingSegmentIds: string[];
}

export interface RunFlaggedTranscriptRerenderRetriesAcrossSectionsOptions<
  T extends SegmentValidationLike,
> {
  initialRowsBySection: Record<string, T[]>;
  thresholdPercent: number;
  maxRetries: number;
  startTtsRerender: (segmentIds: string[]) => Promise<string>;
  startAudioSync: (sectionIds: string[]) => Promise<string>;
  waitForJob: (jobId: string) => Promise<void>;
  reloadValidationRowsBySection: () => Promise<Record<string, T[]>>;
  onTtsJobStarted?: (info: {
    attempt: number;
    jobId: string;
    segmentIds: string[];
  }) => void;
  onAudioSyncJobStarted?: (info: {
    attempt: number;
    jobId: string;
    sectionIds: string[];
  }) => void;
}

export interface RunFlaggedTranscriptRerenderRetriesAcrossSectionsResult<
  T extends SegmentValidationLike,
> {
  attemptsCompleted: number;
  finalRowsBySection: Record<string, T[]>;
  remainingSegmentIdsBySection: Record<string, string[]>;
}

function clampThresholdPercent(thresholdPercent: number): number {
  if (!Number.isFinite(thresholdPercent)) {
    return 0;
  }

  return Math.max(0, Math.min(100, thresholdPercent));
}

function clampMaxRetries(maxRetries: number): number {
  if (!Number.isFinite(maxRetries)) {
    return 0;
  }

  return Math.max(0, Math.floor(maxRetries));
}

export function collectFlaggedSegmentsBelowThreshold<T extends SegmentValidationLike>(
  rows: T[],
  thresholdPercent: number,
): string[] {
  const normalizedThreshold = clampThresholdPercent(thresholdPercent);
  const seen = new Set<string>();
  const segmentIds: string[] = [];

  for (const row of rows) {
    if (row.status !== "warn" && row.status !== "fail") {
      continue;
    }

    if (typeof row.matchRatio !== "number") {
      continue;
    }

    if (row.matchRatio * 100 >= normalizedThreshold) {
      continue;
    }

    if (seen.has(row.segmentId)) {
      continue;
    }

    seen.add(row.segmentId);
    segmentIds.push(row.segmentId);
  }

  return segmentIds;
}

export function collectFlaggedSegmentsBelowThresholdBySection<
  T extends SegmentValidationLike,
>(
  rowsBySection: Record<string, T[]>,
  thresholdPercent: number,
): Record<string, string[]> {
  const results: Record<string, string[]> = {};

  for (const [sectionId, rows] of Object.entries(rowsBySection)) {
    const segmentIds = collectFlaggedSegmentsBelowThreshold(rows, thresholdPercent);
    if (segmentIds.length > 0) {
      results[sectionId] = segmentIds;
    }
  }

  return results;
}

export async function runFlaggedTranscriptRerenderRetries<T extends SegmentValidationLike>(
  options: RunFlaggedTranscriptRerenderRetriesOptions<T>,
): Promise<RunFlaggedTranscriptRerenderRetriesResult<T>> {
  const maxRetries = clampMaxRetries(options.maxRetries);
  let attemptsCompleted = 0;
  let currentRows = options.initialRows;
  let remainingSegmentIds = collectFlaggedSegmentsBelowThreshold(
    currentRows,
    options.thresholdPercent,
  );

  while (attemptsCompleted < maxRetries && remainingSegmentIds.length > 0) {
    const attempt = attemptsCompleted + 1;
    const ttsJobId = await options.startTtsRerender(remainingSegmentIds);
    options.onTtsJobStarted?.({
      attempt,
      jobId: ttsJobId,
      segmentIds: remainingSegmentIds,
    });
    await options.waitForJob(ttsJobId);

    const syncJobId = await options.startAudioSync(options.sectionId);
    options.onAudioSyncJobStarted?.({
      attempt,
      jobId: syncJobId,
      sectionId: options.sectionId,
    });
    await options.waitForJob(syncJobId);

    attemptsCompleted = attempt;
    currentRows = await options.reloadValidationRows();
    remainingSegmentIds = collectFlaggedSegmentsBelowThreshold(
      currentRows,
      options.thresholdPercent,
    );
  }

  return {
    attemptsCompleted,
    finalRows: currentRows,
    remainingSegmentIds,
  };
}

export async function runFlaggedTranscriptRerenderRetriesAcrossSections<
  T extends SegmentValidationLike,
>(
  options: RunFlaggedTranscriptRerenderRetriesAcrossSectionsOptions<T>,
): Promise<RunFlaggedTranscriptRerenderRetriesAcrossSectionsResult<T>> {
  const maxRetries = clampMaxRetries(options.maxRetries);
  let attemptsCompleted = 0;
  let currentRowsBySection = options.initialRowsBySection;
  let remainingSegmentIdsBySection = collectFlaggedSegmentsBelowThresholdBySection(
    currentRowsBySection,
    options.thresholdPercent,
  );

  while (
    attemptsCompleted < maxRetries &&
    Object.keys(remainingSegmentIdsBySection).length > 0
  ) {
    const attempt = attemptsCompleted + 1;
    const segmentIds = Object.values(remainingSegmentIdsBySection).flat();
    const sectionIds = Object.keys(remainingSegmentIdsBySection);

    const ttsJobId = await options.startTtsRerender(segmentIds);
    options.onTtsJobStarted?.({
      attempt,
      jobId: ttsJobId,
      segmentIds,
    });
    await options.waitForJob(ttsJobId);

    const syncJobId = await options.startAudioSync(sectionIds);
    options.onAudioSyncJobStarted?.({
      attempt,
      jobId: syncJobId,
      sectionIds,
    });
    await options.waitForJob(syncJobId);

    attemptsCompleted = attempt;
    currentRowsBySection = await options.reloadValidationRowsBySection();
    remainingSegmentIdsBySection = collectFlaggedSegmentsBelowThresholdBySection(
      currentRowsBySection,
      options.thresholdPercent,
    );
  }

  return {
    attemptsCompleted,
    finalRowsBySection: currentRowsBySection,
    remainingSegmentIdsBySection,
  };
}
