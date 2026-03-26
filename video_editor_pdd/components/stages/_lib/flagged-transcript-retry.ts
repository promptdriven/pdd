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
  continueOnAudioSyncError?: boolean;
  reloadValidationRows: () => Promise<T[]>;
  captureSegmentStates?: (segmentIds: string[]) => Promise<Record<string, string>>;
  restoreSegmentStates?: (snapshots: Record<string, string>) => Promise<void>;
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
  continueOnAudioSyncError?: boolean;
  reloadValidationRowsBySection: () => Promise<Record<string, T[]>>;
  captureSegmentStates?: (segmentIds: string[]) => Promise<Record<string, string>>;
  restoreSegmentStates?: (snapshots: Record<string, string>) => Promise<void>;
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

function getRowMatchRatio<T extends SegmentValidationLike>(
  rows: T[],
  segmentId: string,
): number {
  const row = rows.find((candidate) => candidate.segmentId === segmentId);
  return typeof row?.matchRatio === "number" ? row.matchRatio : -1;
}

function getRowsBySectionMatchRatio<T extends SegmentValidationLike>(
  rowsBySection: Record<string, T[]>,
  segmentId: string,
): number {
  for (const rows of Object.values(rowsBySection)) {
    const ratio = getRowMatchRatio(rows, segmentId);
    if (ratio >= 0) {
      return ratio;
    }
  }

  return -1;
}

function canTrackBestSegmentStates(
  captureSegmentStates?: (segmentIds: string[]) => Promise<Record<string, string>>,
  restoreSegmentStates?: (snapshots: Record<string, string>) => Promise<void>,
): captureSegmentStates is (segmentIds: string[]) => Promise<Record<string, string>> {
  return typeof captureSegmentStates === "function" && typeof restoreSegmentStates === "function";
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
  const trackedSegmentIds = collectFlaggedSegmentsBelowThreshold(
    currentRows,
    options.thresholdPercent,
  );
  let remainingSegmentIds = collectFlaggedSegmentsBelowThreshold(
    currentRows,
    options.thresholdPercent,
  );
  const trackBestSegmentStates = canTrackBestSegmentStates(
    options.captureSegmentStates,
    options.restoreSegmentStates,
  );
  const bestScoresBySegment: Record<string, number> = {};
  let bestStatesBySegment: Record<string, string> = {};

  if (trackBestSegmentStates && trackedSegmentIds.length > 0) {
    for (const segmentId of trackedSegmentIds) {
      bestScoresBySegment[segmentId] = getRowMatchRatio(currentRows, segmentId);
    }
    bestStatesBySegment = await options.captureSegmentStates(trackedSegmentIds);
  }

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
    try {
      await options.waitForJob(syncJobId);
    } catch (error) {
      if (!options.continueOnAudioSyncError) {
        throw error;
      }
    }

    attemptsCompleted = attempt;
    currentRows = await options.reloadValidationRows();
    if (trackBestSegmentStates && trackedSegmentIds.length > 0) {
      const capturedStates = await options.captureSegmentStates(trackedSegmentIds);
      for (const segmentId of trackedSegmentIds) {
        const nextScore = getRowMatchRatio(currentRows, segmentId);
        if (nextScore > (bestScoresBySegment[segmentId] ?? -1)) {
          bestScoresBySegment[segmentId] = nextScore;
          if (capturedStates[segmentId]) {
            bestStatesBySegment[segmentId] = capturedStates[segmentId];
          }
        }
      }
    }
    remainingSegmentIds = collectFlaggedSegmentsBelowThreshold(
      currentRows,
      options.thresholdPercent,
    );
  }

  if (trackBestSegmentStates && attemptsCompleted > 0 && trackedSegmentIds.length > 0) {
    await options.restoreSegmentStates(bestStatesBySegment);
    const syncJobId = await options.startAudioSync(options.sectionId);
    try {
      await options.waitForJob(syncJobId);
    } catch (error) {
      if (!options.continueOnAudioSyncError) {
        throw error;
      }
    }
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
  const trackedSegmentIdsBySection = collectFlaggedSegmentsBelowThresholdBySection(
    currentRowsBySection,
    options.thresholdPercent,
  );
  const trackedSectionIds = Object.keys(trackedSegmentIdsBySection);
  const trackedSegmentIds = Object.values(trackedSegmentIdsBySection).flat();
  let remainingSegmentIdsBySection = collectFlaggedSegmentsBelowThresholdBySection(
    currentRowsBySection,
    options.thresholdPercent,
  );
  const trackBestSegmentStates = canTrackBestSegmentStates(
    options.captureSegmentStates,
    options.restoreSegmentStates,
  );
  const bestScoresBySegment: Record<string, number> = {};
  let bestStatesBySegment: Record<string, string> = {};

  if (trackBestSegmentStates && trackedSegmentIds.length > 0) {
    for (const segmentId of trackedSegmentIds) {
      bestScoresBySegment[segmentId] = getRowsBySectionMatchRatio(
        currentRowsBySection,
        segmentId,
      );
    }
    bestStatesBySegment = await options.captureSegmentStates(trackedSegmentIds);
  }

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
    try {
      await options.waitForJob(syncJobId);
    } catch (error) {
      if (!options.continueOnAudioSyncError) {
        throw error;
      }
    }

    attemptsCompleted = attempt;
    currentRowsBySection = await options.reloadValidationRowsBySection();
    if (trackBestSegmentStates && trackedSegmentIds.length > 0) {
      const capturedStates = await options.captureSegmentStates(trackedSegmentIds);
      for (const segmentId of trackedSegmentIds) {
        const nextScore = getRowsBySectionMatchRatio(currentRowsBySection, segmentId);
        if (nextScore > (bestScoresBySegment[segmentId] ?? -1)) {
          bestScoresBySegment[segmentId] = nextScore;
          if (capturedStates[segmentId]) {
            bestStatesBySegment[segmentId] = capturedStates[segmentId];
          }
        }
      }
    }
    remainingSegmentIdsBySection = collectFlaggedSegmentsBelowThresholdBySection(
      currentRowsBySection,
      options.thresholdPercent,
    );
  }

  if (trackBestSegmentStates && attemptsCompleted > 0 && trackedSegmentIds.length > 0) {
    await options.restoreSegmentStates(bestStatesBySegment);
    const syncJobId = await options.startAudioSync(trackedSectionIds);
    try {
      await options.waitForJob(syncJobId);
    } catch (error) {
      if (!options.continueOnAudioSyncError) {
        throw error;
      }
    }
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
