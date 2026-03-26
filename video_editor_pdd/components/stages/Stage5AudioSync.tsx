'use client';

import React, { useEffect, useMemo, useRef, useState } from 'react';
import type { ProjectConfig, Section } from '../../lib/types';
import {
  fillMissingAudioSyncSectionGroups,
  normalizeAudioSyncSectionGroups,
  toSegmentRangeSectionGroups,
} from './_lib/audio-sync-automation';
import {
  collectFlaggedSegmentsBelowThresholdBySection,
  collectFlaggedSegmentsBelowThreshold,
  runFlaggedTranscriptRerenderRetriesAcrossSections,
  runFlaggedTranscriptRerenderRetries,
} from './_lib/flagged-transcript-retry';
import {
  loadSegmentPreviewAudio,
  resetSegmentPreviewAudio,
} from './_lib/segment-audio-preview';
import {
  captureSegmentAudioSnapshots,
  restoreSegmentAudioSnapshots,
} from './_lib/segment-audio-snapshots';
import PipelineAdvanceButton from '../PipelineAdvanceButton';
import SseLogPanel from '../SseLogPanel';
import { extractJobIdFromSse, waitForJobCompletion } from '@/lib/client/sse-utils';

interface Stage5AudioSyncProps {
  onAdvance: () => void;
}

interface WordTimestamp {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
}

interface SegmentValidation {
  segmentId: string;
  expectedText: string;
  actualText: string;
  matchRatio: number | null;
  status: 'pass' | 'warn' | 'fail' | 'skip';
  expectedWordCount?: number;
  actualWordCount?: number;
}

interface SegmentValidationSummary {
  passCount: number;
  warnCount: number;
  failCount: number;
  skipCount: number;
}

interface AudioSyncArtifactState {
  stale: boolean;
  message: string | null;
  latestAudioUpdatedAtMs?: number;
  syncUpdatedAtMs?: number;
}

interface BatchRetryProgressState {
  mode: 'section' | 'all-sections';
  phase: 'preparing' | 'rerender' | 'audio-sync';
  attempt: number;
  maxRetries: number;
  currentSegmentCount: number;
  currentSectionCount: number;
}

const EMPTY_VALIDATION_SUMMARY: SegmentValidationSummary = {
  passCount: 0,
  warnCount: 0,
  failCount: 0,
  skipCount: 0,
};

const FRESH_AUDIO_SYNC_ARTIFACT_STATE: AudioSyncArtifactState = {
  stale: false,
  message: null,
};

const EMPTY_SECTIONS: Section[] = [];
const ROW_HEIGHT = 32;
const VIEWPORT_HEIGHT = 320;

export default function Stage5AudioSync({ onAdvance }: Stage5AudioSyncProps) {
  const [project, setProject] = useState<ProjectConfig | null>(null);
  const [loadingProject, setLoadingProject] = useState(true);
  const [projectError, setProjectError] = useState<string | null>(null);
  const sections: Section[] = project?.sections ?? EMPTY_SECTIONS;

  const [sectionGroups, setSectionGroups] = useState<Record<string, string[]>>(
    {}
  );
  const [savingConfig, setSavingConfig] = useState(false);

  const [jobId, setJobId] = useState<string | null>(null);

  const [selectedSectionId, setSelectedSectionId] = useState<string>('');
  const [timestamps, setTimestamps] = useState<WordTimestamp[]>([]);
  const [validationRows, setValidationRows] = useState<SegmentValidation[]>([]);
  const [validationSummary, setValidationSummary] = useState<SegmentValidationSummary>(
    EMPTY_VALIDATION_SUMMARY
  );
  const [retryMatchThresholdPercent, setRetryMatchThresholdPercent] = useState(94);
  const [retryMaxAttempts, setRetryMaxAttempts] = useState(2);
  const [batchValidationRerenderJobId, setBatchValidationRerenderJobId] = useState<string | null>(null);
  const [batchValidationSyncJobId, setBatchValidationSyncJobId] = useState<string | null>(null);
  const [batchRetryRunning, setBatchRetryRunning] = useState(false);
  const [batchRetryMessage, setBatchRetryMessage] = useState<string | null>(null);
  const [batchRetryProgress, setBatchRetryProgress] = useState<BatchRetryProgressState | null>(
    null
  );
  const [artifactState, setArtifactState] = useState<AudioSyncArtifactState>(
    FRESH_AUDIO_SYNC_ARTIFACT_STATE
  );
  const [allValidationRowsBySection, setAllValidationRowsBySection] = useState<
    Record<string, SegmentValidation[]>
  >({});
  const [projectWideStaleSectionIds, setProjectWideStaleSectionIds] = useState<string[]>([]);
  const [loadingAllValidationRows, setLoadingAllValidationRows] = useState(false);
  const [loadingTimestamps, setLoadingTimestamps] = useState(false);
  const [search, setSearch] = useState('');
  const [validationJobIds, setValidationJobIds] = useState<Record<string, string | null>>({});
  const [validationSyncJobIds, setValidationSyncJobIds] = useState<Record<string, string | null>>({});
  const [dataReloadVersion, setDataReloadVersion] = useState(0);
  const [playingSegmentId, setPlayingSegmentId] = useState<string | null>(null);

  const [scrollTop, setScrollTop] = useState(0);
  const scrollRef = useRef<HTMLDivElement>(null);
  const previewAudioRef = useRef<HTMLAudioElement | null>(null);
  const previewAudioObjectUrlRef = useRef<string | null>(null);

  const [detecting, setDetecting] = useState(false);
  const [detectError, setDetectError] = useState<string | null>(null);
  const [unmatchedSegments, setUnmatchedSegments] = useState<string[]>([]);
  const [overwriteExisting, setOverwriteExisting] = useState(false);
  const [autoFilledSections, setAutoFilledSections] = useState<string[]>([]);

  const reloadSectionArtifacts = async (sectionId: string) => {
    setLoadingTimestamps(true);
    try {
      const res = await fetch(
        `/api/pipeline/audio-sync/timestamps?section=${encodeURIComponent(
          sectionId
        )}`
      );
      if (!res.ok) {
        setTimestamps([]);
        setValidationRows([]);
        setValidationSummary(EMPTY_VALIDATION_SUMMARY);
        setArtifactState(FRESH_AUDIO_SYNC_ARTIFACT_STATE);
        return [];
      }

      const data = await res.json();
      const list = Array.isArray(data) ? data : (Array.isArray(data?.words) ? data.words : []);
      const nextArtifactState: AudioSyncArtifactState =
        data?.artifactState && typeof data.artifactState === 'object'
          ? {
              stale: data.artifactState.stale === true,
              message:
                typeof data.artifactState.message === 'string'
                  ? data.artifactState.message
                  : null,
              latestAudioUpdatedAtMs:
                typeof data.artifactState.latestAudioUpdatedAtMs === 'number'
                  ? data.artifactState.latestAudioUpdatedAtMs
                  : undefined,
              syncUpdatedAtMs:
                typeof data.artifactState.syncUpdatedAtMs === 'number'
                  ? data.artifactState.syncUpdatedAtMs
                  : undefined,
            }
          : FRESH_AUDIO_SYNC_ARTIFACT_STATE;
      const nextValidationRows = Array.isArray(data?.validation?.segments)
        ? data.validation.segments
        : [];
      const nextValidationSummary =
        data?.validation?.summary ?? EMPTY_VALIDATION_SUMMARY;

      setArtifactState(nextArtifactState);
      if (nextArtifactState.stale) {
        setTimestamps([]);
        setValidationRows(nextValidationRows);
        setValidationSummary(nextValidationSummary);
        return nextValidationRows as SegmentValidation[];
      }

      setTimestamps(list);
      setValidationRows(Array.isArray(data?.validation?.segments) ? data.validation.segments : []);
      setValidationSummary(data?.validation?.summary ?? EMPTY_VALIDATION_SUMMARY);
      return nextValidationRows as SegmentValidation[];
    } catch {
      setTimestamps([]);
      setValidationRows([]);
      setValidationSummary(EMPTY_VALIDATION_SUMMARY);
      setArtifactState(FRESH_AUDIO_SYNC_ARTIFACT_STATE);
      return [];
    } finally {
      setLoadingTimestamps(false);
    }
  };

  const fetchValidationDataForSection = async (sectionId: string) => {
    const res = await fetch(
      `/api/pipeline/audio-sync/timestamps?section=${encodeURIComponent(
        sectionId
      )}`
    );
    if (!res.ok) {
      return {
        artifactState: FRESH_AUDIO_SYNC_ARTIFACT_STATE,
        rows: [] as SegmentValidation[],
      };
    }

    const data = await res.json();
    const nextArtifactState: AudioSyncArtifactState =
      data?.artifactState && typeof data.artifactState === 'object'
        ? {
            stale: data.artifactState.stale === true,
            message:
              typeof data.artifactState.message === 'string'
                ? data.artifactState.message
                : null,
            latestAudioUpdatedAtMs:
              typeof data.artifactState.latestAudioUpdatedAtMs === 'number'
                ? data.artifactState.latestAudioUpdatedAtMs
                : undefined,
            syncUpdatedAtMs:
              typeof data.artifactState.syncUpdatedAtMs === 'number'
                ? data.artifactState.syncUpdatedAtMs
                : undefined,
          }
        : FRESH_AUDIO_SYNC_ARTIFACT_STATE;

    return {
      artifactState: nextArtifactState,
      rows: Array.isArray(data?.validation?.segments)
        ? (data.validation.segments as SegmentValidation[])
        : [],
    };
  };

  const fetchValidationRowsForSection = async (sectionId: string) => {
    const { rows } = await fetchValidationDataForSection(sectionId);
    return rows;
  };

  // ----------------------------------------
  // Load project config
  // ----------------------------------------
  useEffect(() => {
    let active = true;
    (async () => {
      try {
        setLoadingProject(true);
        const res = await fetch('/api/project');
        const data = (await res.json()) as ProjectConfig;
        if (!active) return;
        setProject(data);
        const normalized = normalizeAudioSyncSectionGroups(
          data.audioSync?.sectionGroups ?? {}
        );
        setSectionGroups(normalized);
        // default section
        if (data.sections?.length > 0) {
          setSelectedSectionId(data.sections[0].id);
        }
      } catch (err: any) {
        if (!active) return;
        setProjectError(err?.message ?? 'Failed to load project');
      } finally {
        if (active) setLoadingProject(false);
      }
    })();

    return () => {
      active = false;
    };
  }, []);

  // ----------------------------------------
  // Load timestamps when section changes
  // ----------------------------------------
  useEffect(() => {
    if (!selectedSectionId) return;
    let active = true;
    (async () => {
      const rows = await reloadSectionArtifacts(selectedSectionId);
      if (!active) return;
      void rows;
    })();
    return () => {
      active = false;
    };
  }, [dataReloadVersion, selectedSectionId]);

  useEffect(() => {
    return () => {
      const audio = previewAudioRef.current;
      if (audio) {
        previewAudioObjectUrlRef.current = resetSegmentPreviewAudio(
          audio,
          previewAudioObjectUrlRef.current
        );
      }
    };
  }, []);

  useEffect(() => {
    if (sections.length === 0) {
      setAllValidationRowsBySection((prev) =>
        Object.keys(prev).length === 0 ? prev : {}
      );
      setProjectWideStaleSectionIds((prev) => (prev.length === 0 ? prev : []));
      setLoadingAllValidationRows(false);
      return;
    }

    let active = true;
    (async () => {
      setLoadingAllValidationRows(true);
      try {
        const nextEntries = await Promise.all(
          sections.map(async (section) => {
            if (section.id === selectedSectionId) {
              return [
                section.id,
                {
                  artifactState,
                  rows: validationRows,
                },
              ] as const;
            }

            return [
              section.id,
              await fetchValidationDataForSection(section.id),
            ] as const;
          })
        );

        if (!active) return;
        setAllValidationRowsBySection(
          Object.fromEntries(
            nextEntries.map(([sectionId, data]) => [sectionId, data.rows] as const)
          )
        );
        setProjectWideStaleSectionIds(
          nextEntries
            .filter(([, data]) => data.artifactState.stale)
            .map(([sectionId]) => sectionId)
        );
      } finally {
        if (active) {
          setLoadingAllValidationRows(false);
        }
      }
    })();

    return () => {
      active = false;
    };
  }, [sections, selectedSectionId, validationRows, artifactState, dataReloadVersion]);

  // ----------------------------------------
  // Derived values
  // ----------------------------------------
  const filteredWords = useMemo(() => {
    const term = search.toLowerCase();
    return timestamps.filter((w) => w.word.toLowerCase().includes(term));
  }, [timestamps, search]);
  const flaggedValidationRows = useMemo(
    () => validationRows.filter((row) => row.status !== 'pass' && row.status !== 'skip'),
    [validationRows]
  );
  const retryableValidationSegmentIds = useMemo(
    () =>
      collectFlaggedSegmentsBelowThreshold(
        flaggedValidationRows,
        retryMatchThresholdPercent
      ),
    [flaggedValidationRows, retryMatchThresholdPercent]
  );
  const belowThresholdValidationRows = useMemo(() => {
    const retryableSet = new Set(retryableValidationSegmentIds);
    return flaggedValidationRows.filter((row) => retryableSet.has(row.segmentId));
  }, [flaggedValidationRows, retryableValidationSegmentIds]);
  const projectWideRetryableSegmentIdsBySection = useMemo(
    () =>
      collectFlaggedSegmentsBelowThresholdBySection(
        allValidationRowsBySection,
        retryMatchThresholdPercent
      ),
    [allValidationRowsBySection, retryMatchThresholdPercent]
  );
  const projectWideRetryableSectionIds = useMemo(
    () => Object.keys(projectWideRetryableSegmentIdsBySection),
    [projectWideRetryableSegmentIdsBySection]
  );
  const totalProjectWideRetryableSegments = useMemo(
    () =>
      Object.values(projectWideRetryableSegmentIdsBySection).reduce(
        (sum, segmentIds) => sum + segmentIds.length,
        0
      ),
    [projectWideRetryableSegmentIdsBySection]
  );

  const totalWords = timestamps.length;
  const visibleCount = Math.ceil(VIEWPORT_HEIGHT / ROW_HEIGHT) + 10;
  const startIndex = Math.max(0, Math.floor(scrollTop / ROW_HEIGHT) - 5);
  const endIndex = Math.min(filteredWords.length, startIndex + visibleCount);
  const visibleWords = filteredWords.slice(startIndex, endIndex);
  const offsetY = startIndex * ROW_HEIGHT;
  const totalHeight = filteredWords.length * ROW_HEIGHT;

  // ----------------------------------------
  // Handlers
  // ----------------------------------------
  const handleGroupChange = (sectionId: string, value: string) => {
    const segments = value
      .split(',')
      .map((s) => s.trim())
      .filter(Boolean);
    setSectionGroups((prev) => ({ ...prev, [sectionId]: segments }));
  };

  const handleDetectSegments = async () => {
    setDetecting(true);
    setDetectError(null);
    setUnmatchedSegments([]);
    try {
      const res = await fetch('/api/pipeline/tts-render/segments');
      if (!res.ok) throw new Error('Failed to fetch segments');
      const data = await res.json();
      const allSegments: { id: string }[] = data.segments ?? [];

      const sectionIds = sections.map((s) => s.id);
      // Sort by length descending for longest-match-first
      const sortedSectionIds = [...sectionIds].sort((a, b) => b.length - a.length);

      const existingGroups = overwriteExisting
        ? Object.fromEntries(sections.map((section) => [section.id, []]))
        : sectionGroups;
      const detection = fillMissingAudioSyncSectionGroups({
        sections,
        existingGroups,
        segments: allSegments,
      });

      setUnmatchedSegments(detection.unmatchedSegments);
      setSectionGroups(detection.groups);
      setAutoFilledSections(detection.filledSections);
      setTimeout(() => setAutoFilledSections([]), 5000);
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to detect segments');
    } finally {
      setDetecting(false);
    }
  };

  const handleSaveConfig = async () => {
    setSavingConfig(true);
    setDetectError(null);
    try {
      const rangeGroups = toSegmentRangeSectionGroups(sectionGroups);
      const res = await fetch('/api/project', {
        method: 'PUT',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          audioSync: { ...project?.audioSync, sectionGroups: rangeGroups },
        }),
      });
      if (!res.ok) {
        const data = await res.json().catch(() => ({}));
        throw new Error(data.error || 'Failed to save config');
      }
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to save config');
    } finally {
      setSavingConfig(false);
    }
  };

  const handleRunAudioSync = async () => {
    setDetectError(null);
    try {
      const res = await fetch('/api/pipeline/audio-sync/run', {
        method: 'POST',
      });
      if (!res.ok) {
        throw new Error('Failed to start audio sync.');
      }

      const nextJobId = await extractJobIdFromSse(res);
      if (!nextJobId) {
        throw new Error('Failed to get audio sync job ID.');
      }
      setJobId(nextJobId);
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to start audio sync');
    }
  };

  const handleSseDone = () => {
    // Auto-load timestamps for first section after run completes
    if (project?.sections?.length && !selectedSectionId) {
      setSelectedSectionId(project.sections[0].id);
    }
    setDataReloadVersion((prev) => prev + 1);
  };

  const handleRerenderSegment = async (segmentId: string) => {
    setDetectError(null);
    try {
      const res = await fetch('/api/pipeline/tts-render/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ segments: [segmentId], skipDependencies: true }),
      });
      if (!res.ok) {
        throw new Error('Failed to start TTS rerender.');
      }

      const rowJobId = await extractJobIdFromSse(res);
      if (!rowJobId) {
        throw new Error('Failed to get TTS rerender job ID.');
      }
      setValidationJobIds((prev) => ({ ...prev, [segmentId]: rowJobId }));
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to rerender segment');
    }
  };

  const handleValidationRerenderDone = async (segmentId: string) => {
    if (!selectedSectionId) {
      return;
    }

    try {
      const res = await fetch('/api/pipeline/audio-sync/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          sections: [selectedSectionId],
          allowValidationFailures: true,
          skipDependencies: true,
        }),
      });
      if (!res.ok) {
        throw new Error('Failed to rerun audio sync.');
      }

      const syncJobId = await extractJobIdFromSse(res);
      if (!syncJobId) {
        throw new Error('Failed to get audio sync job ID.');
      }
      setValidationSyncJobIds((prev) => ({ ...prev, [segmentId]: syncJobId }));
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to rerun audio sync');
    }
  };

  const handleValidationSyncDone = (segmentId: string) => {
    setValidationJobIds((prev) => ({ ...prev, [segmentId]: null }));
    setValidationSyncJobIds((prev) => ({ ...prev, [segmentId]: null }));
    setDataReloadVersion((prev) => prev + 1);
  };

  const handleRetryFlaggedSegments = async () => {
    if (!selectedSectionId) {
      return;
    }

    if (retryableValidationSegmentIds.length === 0) {
      setBatchRetryMessage('No flagged transcript mismatches are below the current threshold.');
      return;
    }

    setDetectError(null);
    setBatchRetryMessage(null);
    setBatchRetryRunning(true);
    setBatchValidationRerenderJobId(null);
    setBatchValidationSyncJobId(null);
    setBatchRetryProgress({
      mode: 'section',
      phase: 'preparing',
      attempt: 1,
      maxRetries: retryMaxAttempts,
      currentSegmentCount: retryableValidationSegmentIds.length,
      currentSectionCount: 1,
    });

    try {
      const result = await runFlaggedTranscriptRerenderRetries({
        initialRows: flaggedValidationRows,
        thresholdPercent: retryMatchThresholdPercent,
        maxRetries: retryMaxAttempts,
        sectionId: selectedSectionId,
        continueOnAudioSyncError: true,
        startTtsRerender: async (segmentIds) => {
          const res = await fetch('/api/pipeline/tts-render/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ segments: segmentIds, skipDependencies: true }),
          });
          if (!res.ok) {
            throw new Error('Failed to start batch TTS rerender.');
          }

          const nextJobId = await extractJobIdFromSse(res);
          if (!nextJobId) {
            throw new Error('Failed to get batch TTS rerender job ID.');
          }

          setBatchValidationRerenderJobId(nextJobId);
          return nextJobId;
        },
        startAudioSync: async (sectionId) => {
          const res = await fetch('/api/pipeline/audio-sync/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
              sections: [sectionId],
              allowValidationFailures: true,
              skipDependencies: true,
            }),
          });
          if (!res.ok) {
            throw new Error('Failed to start batch audio sync rerun.');
          }

          const nextJobId = await extractJobIdFromSse(res);
          if (!nextJobId) {
            throw new Error('Failed to get batch audio sync job ID.');
          }

          setBatchValidationSyncJobId(nextJobId);
          return nextJobId;
        },
        waitForJob: waitForJobCompletion,
        onTtsJobStarted: ({ attempt, segmentIds }) => {
          setBatchRetryProgress({
            mode: 'section',
            phase: 'rerender',
            attempt,
            maxRetries: retryMaxAttempts,
            currentSegmentCount: segmentIds.length,
            currentSectionCount: 1,
          });
        },
        onAudioSyncJobStarted: ({ attempt }) => {
          setBatchRetryProgress({
            mode: 'section',
            phase: 'audio-sync',
            attempt,
            maxRetries: retryMaxAttempts,
            currentSegmentCount: retryableValidationSegmentIds.length,
            currentSectionCount: 1,
          });
        },
        captureSegmentStates: async (segmentIds) =>
          captureSegmentAudioSnapshots({ segmentIds }),
        restoreSegmentStates: async (snapshots) =>
          restoreSegmentAudioSnapshots({ snapshots }),
        reloadValidationRows: async () => {
          const rows = await reloadSectionArtifacts(selectedSectionId);
          setDataReloadVersion((prev) => prev + 1);
          return rows;
        },
      });

      setBatchRetryMessage(
        result.remainingSegmentIds.length === 0
          ? `Retry complete after ${result.attemptsCompleted} attempt${result.attemptsCompleted === 1 ? '' : 's'}. Before: ${retryableValidationSegmentIds.length} segment${retryableValidationSegmentIds.length === 1 ? '' : 's'} below threshold. After: ${result.remainingSegmentIds.length}.`
          : `Stopped after ${result.attemptsCompleted} attempt${result.attemptsCompleted === 1 ? '' : 's'}. Before: ${retryableValidationSegmentIds.length} segment${retryableValidationSegmentIds.length === 1 ? '' : 's'} below threshold. After: ${result.remainingSegmentIds.length} segment${result.remainingSegmentIds.length === 1 ? '' : 's'} still below threshold.`
      );
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to retry flagged transcript mismatches');
    } finally {
      setBatchRetryRunning(false);
      setBatchRetryProgress(null);
    }
  };

  const handleRetryFlaggedSegmentsAcrossAllSections = async () => {
    if (sections.length === 0) {
      return;
    }

    setDetectError(null);
    setBatchRetryMessage(null);
    setBatchRetryRunning(true);
    setBatchValidationRerenderJobId(null);
    setBatchValidationSyncJobId(null);
    setBatchRetryProgress({
      mode: 'all-sections',
      phase: 'preparing',
      attempt: 1,
      maxRetries: retryMaxAttempts,
      currentSegmentCount: 0,
      currentSectionCount: sections.length,
    });

    try {
      const initialRowsBySection = Object.fromEntries(
        await Promise.all(
          sections.map(async (section) => {
            if (section.id === selectedSectionId) {
              return [section.id, validationRows] as const;
            }

            const { rows } = await fetchValidationDataForSection(section.id);
            return [section.id, rows] as const;
          })
        )
      );

      const retryableBySection = collectFlaggedSegmentsBelowThresholdBySection(
        initialRowsBySection,
        retryMatchThresholdPercent
      );
      const retryableSectionIds = Object.keys(retryableBySection);
      const retryableSegmentCount = Object.values(retryableBySection).reduce(
        (sum, segmentIds) => sum + segmentIds.length,
        0
      );

      setBatchRetryProgress({
        mode: 'all-sections',
        phase: 'preparing',
        attempt: 1,
        maxRetries: retryMaxAttempts,
        currentSegmentCount: retryableSegmentCount,
        currentSectionCount: retryableSectionIds.length,
      });

      if (retryableSectionIds.length === 0) {
        setBatchRetryMessage('No flagged transcript mismatches are below the current threshold in any section.');
        return;
      }

      const result = await runFlaggedTranscriptRerenderRetriesAcrossSections({
        initialRowsBySection,
        thresholdPercent: retryMatchThresholdPercent,
        maxRetries: retryMaxAttempts,
        continueOnAudioSyncError: true,
        startTtsRerender: async (segmentIds) => {
          const res = await fetch('/api/pipeline/tts-render/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ segments: segmentIds, skipDependencies: true }),
          });
          if (!res.ok) {
            throw new Error('Failed to start all-sections TTS rerender.');
          }

          const nextJobId = await extractJobIdFromSse(res);
          if (!nextJobId) {
            throw new Error('Failed to get all-sections TTS rerender job ID.');
          }

          setBatchValidationRerenderJobId(nextJobId);
          return nextJobId;
        },
        startAudioSync: async (sectionIds) => {
          const res = await fetch('/api/pipeline/audio-sync/run', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
              sections: sectionIds,
              allowValidationFailures: true,
              skipDependencies: true,
            }),
          });
          if (!res.ok) {
            throw new Error('Failed to start all-sections audio sync rerun.');
          }

          const nextJobId = await extractJobIdFromSse(res);
          if (!nextJobId) {
            throw new Error('Failed to get all-sections audio sync job ID.');
          }

          setBatchValidationSyncJobId(nextJobId);
          return nextJobId;
        },
        waitForJob: waitForJobCompletion,
        onTtsJobStarted: ({ attempt, segmentIds }) => {
          setBatchRetryProgress({
            mode: 'all-sections',
            phase: 'rerender',
            attempt,
            maxRetries: retryMaxAttempts,
            currentSegmentCount: segmentIds.length,
            currentSectionCount: retryableSectionIds.length,
          });
        },
        onAudioSyncJobStarted: ({ attempt, sectionIds }) => {
          setBatchRetryProgress({
            mode: 'all-sections',
            phase: 'audio-sync',
            attempt,
            maxRetries: retryMaxAttempts,
            currentSegmentCount: retryableSegmentCount,
            currentSectionCount: sectionIds.length,
          });
        },
        captureSegmentStates: async (segmentIds) =>
          captureSegmentAudioSnapshots({ segmentIds }),
        restoreSegmentStates: async (snapshots) =>
          restoreSegmentAudioSnapshots({ snapshots }),
        reloadValidationRowsBySection: async () => {
          const nextRowsBySection = Object.fromEntries(
            await Promise.all(
              retryableSectionIds.map(async (sectionId) => [
                sectionId,
                await fetchValidationRowsForSection(sectionId),
              ] as const)
            )
          );

          if (selectedSectionId in nextRowsBySection) {
            await reloadSectionArtifacts(selectedSectionId);
            setDataReloadVersion((prev) => prev + 1);
          }

          return nextRowsBySection;
        },
      });

      const remainingSectionIds = Object.keys(result.remainingSegmentIdsBySection);
      const remainingSegmentCount = Object.values(result.remainingSegmentIdsBySection).reduce(
        (sum, segmentIds) => sum + segmentIds.length,
        0
      );
      setBatchRetryMessage(
        remainingSectionIds.length === 0
          ? `All-sections retry complete after ${result.attemptsCompleted} attempt${result.attemptsCompleted === 1 ? '' : 's'}. Before: ${retryableSegmentCount} segment${retryableSegmentCount === 1 ? '' : 's'} across ${retryableSectionIds.length} section${retryableSectionIds.length === 1 ? '' : 's'} below threshold. After: ${remainingSegmentCount} across ${remainingSectionIds.length}.`
          : `All-sections retry stopped after ${result.attemptsCompleted} attempt${result.attemptsCompleted === 1 ? '' : 's'}. Before: ${retryableSegmentCount} segment${retryableSegmentCount === 1 ? '' : 's'} across ${retryableSectionIds.length} section${retryableSectionIds.length === 1 ? '' : 's'} below threshold. After: ${remainingSegmentCount} segment${remainingSegmentCount === 1 ? '' : 's'} across ${remainingSectionIds.length} section${remainingSectionIds.length === 1 ? '' : 's'} still below threshold.`
      );
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to retry flagged transcript mismatches across all sections');
    } finally {
      setBatchRetryRunning(false);
      setBatchRetryProgress(null);
    }
  };

  const handlePreviewSegmentAudio = async (segmentId: string) => {
    try {
      const audio = previewAudioRef.current;
      if (!audio) {
        throw new Error('Audio preview unavailable');
      }

      if (playingSegmentId === segmentId) {
        previewAudioObjectUrlRef.current = resetSegmentPreviewAudio(
          audio,
          previewAudioObjectUrlRef.current
        );
        setPlayingSegmentId(null);
        return;
      }

      setDetectError(null);
      previewAudioObjectUrlRef.current = await loadSegmentPreviewAudio({
        audio,
        segmentId,
        previousObjectUrl: previewAudioObjectUrlRef.current,
      });
      setPlayingSegmentId(segmentId);
    } catch (err: any) {
      setDetectError(err?.message ?? 'Failed to play segment audio');
      setPlayingSegmentId(null);
    }
  };

  // ----------------------------------------
  // Render
  // ----------------------------------------
  if (loadingProject) {
    return (
      <div className="p-6 space-y-6">
        <h2 className="text-xl font-semibold">Stage 5 — Audio Sync</h2>
        <div className="text-sm text-slate-500">Loading project…</div>
      </div>
    );
  }

  if (projectError) {
    return (
      <div className="p-6 space-y-6">
        <h2 className="text-xl font-semibold">Stage 5 — Audio Sync</h2>
        <div className="text-sm text-red-500">Error loading project: {projectError}</div>
      </div>
    );
  }

  return (
    <div className="space-y-6">
      <audio
        ref={previewAudioRef}
        className="hidden"
        preload="auto"
        onEnded={() => {
          const audio = previewAudioRef.current;
          if (audio) {
            previewAudioObjectUrlRef.current = resetSegmentPreviewAudio(
              audio,
              previewAudioObjectUrlRef.current
            );
          }
          setPlayingSegmentId(null);
        }}
        onError={() => {
          const audio = previewAudioRef.current;
          if (audio) {
            previewAudioObjectUrlRef.current = resetSegmentPreviewAudio(
              audio,
              previewAudioObjectUrlRef.current
            );
          }
          setPlayingSegmentId(null);
          setDetectError('Failed to load segment audio');
        }}
      />
      <h2 className="text-xl font-semibold">Stage 5 — Audio Sync</h2>
      {/* Top Section: Section Grouping Table */}
      <div className="rounded-lg border border-slate-700 bg-slate-900 p-4 shadow-sm">
        <div className="flex items-center justify-between mb-4">
          <h3 className="text-lg font-semibold text-slate-100">Audio Sync Section Groups</h3>
          <div className="flex items-center gap-2">
            <label className="flex items-center gap-1 text-xs text-slate-400">
              <input
                type="checkbox"
                checked={overwriteExisting}
                onChange={(e) => setOverwriteExisting(e.target.checked)}
              />
              Overwrite existing
            </label>
            <button
              onClick={handleDetectSegments}
              disabled={detecting}
              className="rounded-md bg-amber-600 px-3 py-1.5 text-white text-sm disabled:opacity-50"
            >
              {detecting ? 'Detecting…' : 'Detect Segments'}
            </button>
            <button
              onClick={handleSaveConfig}
              disabled={savingConfig}
              className="rounded-md bg-blue-600 px-3 py-1.5 text-white text-sm disabled:opacity-50"
            >
              {savingConfig ? 'Saving…' : 'Save Config'}
            </button>
            <button
              onClick={handleRunAudioSync}
              className="rounded-md bg-emerald-600 px-3 py-1.5 text-white text-sm"
            >
              Run Audio Sync
            </button>
          </div>
        </div>

        <table className="w-full text-sm border-collapse">
          <thead>
            <tr className="text-left border-b border-slate-700">
              <th className="py-2 text-slate-300">Section</th>
              <th className="py-2 text-slate-300">Segment IDs (comma-separated)</th>
            </tr>
          </thead>
          <tbody>
            {sections.map((section) => (
              <tr key={section.id} className="border-b border-slate-700">
                <td className="py-2 pr-4 font-medium text-slate-200">
                  {section.label}
                  {autoFilledSections.includes(section.id) && (
                    <span className="ml-2 text-xs text-amber-400">(auto-detected)</span>
                  )}
                </td>
                <td className="py-2">
                  <input
                    className="w-full rounded border border-slate-600 bg-slate-800 px-2 py-1 text-sm text-slate-200 placeholder-slate-500"
                    value={(sectionGroups[section.id] ?? []).join(', ')}
                    onChange={(e) =>
                      handleGroupChange(section.id, e.target.value)
                    }
                    placeholder="segment1, segment2, segment3"
                  />
                </td>
              </tr>
            ))}
          </tbody>
        </table>

        {detectError && (
          <div className="mt-3 rounded-md bg-red-900/50 border border-red-700 px-3 py-2 text-sm text-red-300">
            {detectError}
          </div>
        )}

        {unmatchedSegments.length > 0 && (
          <div className="mt-3 rounded-md bg-yellow-900/50 border border-yellow-700 px-3 py-2 text-sm text-yellow-300">
            {unmatchedSegments.length} segment(s) did not match any section:{' '}
            {unmatchedSegments.join(', ')}
          </div>
        )}

        <div className="mt-4">
          <SseLogPanel jobId={jobId} onDone={handleSseDone} />
        </div>
      </div>

      {/* Bottom Section: Word Timestamp Viewer */}
      <div className="rounded-lg border border-slate-700 bg-slate-900 p-4 shadow-sm">
        <div className="flex flex-wrap items-center gap-4 mb-4">
          <h2 className="text-lg font-semibold text-slate-100">Word Timestamp Viewer</h2>

          <div className="flex items-center gap-2">
            <label
              htmlFor="audio-sync-section-select"
              className="text-sm text-slate-300"
            >
              Section:
            </label>
            <select
              id="audio-sync-section-select"
              aria-label="Section"
              data-testid="audio-sync-section-select"
              className="rounded border border-slate-600 bg-slate-800 px-2 py-1 text-sm text-slate-200"
              value={selectedSectionId}
              onChange={(e) => setSelectedSectionId(e.target.value)}
            >
              {sections.map((s) => (
                <option key={s.id} value={s.id}>
                  {s.label}
                </option>
              ))}
            </select>
          </div>

          <input
            className="rounded border border-slate-600 bg-slate-800 px-2 py-1 text-sm text-slate-200 placeholder-slate-500"
            placeholder="Search word…"
            value={search}
            onChange={(e) => setSearch(e.target.value)}
          />

          <div className="text-xs text-slate-400">
            {filteredWords.length} of {totalWords} words
          </div>
        </div>

        <div className="text-xs text-slate-400 mb-2">
          {loadingTimestamps ? 'Loading timestamps…' : ''}
        </div>
            {artifactState.stale && (
              <div className="mb-4 rounded-md border border-amber-500/40 bg-amber-500/10 px-3 py-2 text-sm text-amber-200">
                {artifactState.message ?? 'Audio sync data is stale relative to the current TTS audio. Showing the last available transcript validation results; re-run audio sync for this section.'}
              </div>
            )}

        <div className="mb-4 rounded-lg border border-slate-700 bg-slate-950/60 p-4">
          <div className="mb-3 flex flex-wrap items-center justify-between gap-3">
            <div>
              <h3 className="text-sm font-semibold text-slate-100">Flagged Transcript Mismatches</h3>
              <div className="text-xs text-slate-400">
                pass {validationSummary.passCount} · warn {validationSummary.warnCount} · fail {validationSummary.failCount}
              </div>
            </div>
            <div className="text-xs text-slate-500">
              Re-run audio sync after rerendering to refresh validation.
            </div>
          </div>

          <div className="mb-3 flex flex-wrap items-end gap-3">
            <label className="text-xs text-slate-300">
              <div className="mb-1">Retry Below Match %</div>
              <input
                type="number"
                min={0}
                max={100}
                value={retryMatchThresholdPercent}
                onChange={(e) =>
                  setRetryMatchThresholdPercent(
                    Math.max(0, Math.min(100, Number(e.target.value) || 0))
                  )
                }
                className="w-28 rounded border border-slate-600 bg-slate-800 px-2 py-1 text-sm text-slate-200"
              />
            </label>
            <label className="text-xs text-slate-300">
              <div className="mb-1">Max Retries</div>
              <input
                type="number"
                min={1}
                max={10}
                value={retryMaxAttempts}
                onChange={(e) =>
                  setRetryMaxAttempts(
                    Math.max(1, Math.min(10, Number(e.target.value) || 1))
                  )
                }
                className="w-24 rounded border border-slate-600 bg-slate-800 px-2 py-1 text-sm text-slate-200"
              />
            </label>
            <button
              onClick={handleRetryFlaggedSegments}
              disabled={
                batchRetryRunning ||
                artifactState.stale ||
                retryableValidationSegmentIds.length === 0
              }
              className="inline-flex items-center justify-center rounded-md border border-orange-400/60 bg-orange-600 px-3 py-1.5 text-xs font-medium text-white shadow-sm transition-colors hover:bg-orange-500 disabled:cursor-not-allowed disabled:opacity-50 disabled:hover:bg-orange-600"
            >
              {batchRetryRunning ? 'Retrying…' : 'Retry Flagged Segments'}
            </button>
            <button
              onClick={handleRetryFlaggedSegmentsAcrossAllSections}
              disabled={batchRetryRunning || sections.length === 0}
              className="inline-flex items-center justify-center rounded-md border border-indigo-400/60 bg-indigo-600 px-3 py-1.5 text-xs font-medium text-white shadow-sm transition-colors hover:bg-indigo-500 disabled:cursor-not-allowed disabled:opacity-50 disabled:hover:bg-indigo-600"
            >
              {batchRetryRunning ? 'Retrying…' : 'Retry Across All Sections'}
            </button>
          </div>

          <div className="mb-3 grid gap-3 lg:grid-cols-2">
            <div className="rounded-md border border-slate-800 bg-slate-900/70 p-3">
              <div className="mb-1 text-xs font-semibold uppercase tracking-wide text-slate-400">
                Below Threshold in This Section
              </div>
              <div className="text-sm text-slate-200">
                {retryableValidationSegmentIds.length} segment
                {retryableValidationSegmentIds.length === 1 ? '' : 's'} currently fall below the
                retry threshold for {selectedSectionId || 'this section'}.
              </div>
              {belowThresholdValidationRows.length === 0 ? (
                <div className="mt-2 text-xs text-slate-500">
                  No current-section segments are below the retry threshold.
                </div>
              ) : (
                <div className="mt-2 flex flex-wrap gap-2">
                  {belowThresholdValidationRows.map((row) => (
                    <div
                      key={row.segmentId}
                      className="rounded border border-amber-500/30 bg-amber-500/10 px-2 py-1 text-xs text-amber-200"
                    >
                      {row.segmentId}
                      {typeof row.matchRatio === 'number' && (
                        <span className="ml-1 text-amber-100/80">
                          {(row.matchRatio * 100).toFixed(0)}%
                        </span>
                      )}
                    </div>
                  ))}
                </div>
              )}
            </div>

            <details className="rounded-md border border-slate-800 bg-slate-900/70 p-3">
              <summary className="cursor-pointer list-none">
                <div className="mb-1 text-xs font-semibold uppercase tracking-wide text-slate-400">
                  Below Threshold Across Project
                </div>
                <div className="text-sm text-slate-200">
                  {loadingAllValidationRows
                    ? 'Loading project-wide retry candidates…'
                    : `${totalProjectWideRetryableSegments} segment${
                        totalProjectWideRetryableSegments === 1 ? '' : 's'
                      } across ${projectWideRetryableSectionIds.length} section${
                        projectWideRetryableSectionIds.length === 1 ? '' : 's'
                      } are below the retry threshold.`}
                </div>
                {!loadingAllValidationRows && projectWideStaleSectionIds.length > 0 && (
                  <div className="mt-1 text-xs text-amber-300/90">
                    Includes last available validation results for{' '}
                    {projectWideStaleSectionIds.length} stale section
                    {projectWideStaleSectionIds.length === 1 ? '' : 's'}.
                  </div>
                )}
              </summary>

              <div className="mt-3 space-y-2">
                {projectWideRetryableSectionIds.length === 0 ? (
                  <div className="text-xs text-slate-500">
                    No project-wide segments are below the current retry threshold.
                  </div>
                ) : (
                  projectWideRetryableSectionIds.map((sectionId) => (
                    <div
                      key={sectionId}
                      className="rounded border border-slate-800 bg-slate-950/70 px-3 py-2"
                    >
                      <div className="text-xs font-medium uppercase tracking-wide text-slate-300">
                        {sectionId}
                      </div>
                      <div className="mt-1 flex flex-wrap gap-2">
                        {projectWideRetryableSegmentIdsBySection[sectionId].map((segmentId) => (
                          <span
                            key={segmentId}
                            className="rounded border border-indigo-500/30 bg-indigo-500/10 px-2 py-1 text-xs text-indigo-200"
                          >
                            {segmentId}
                          </span>
                        ))}
                      </div>
                    </div>
                  ))
                )}
              </div>
            </details>
          </div>

          {batchRetryRunning && batchRetryProgress && (
            <div className="mb-3 rounded-md border border-sky-500/30 bg-sky-500/10 px-3 py-3">
              <div className="flex flex-wrap items-center justify-between gap-3 text-xs text-sky-100">
                <div>
                  Retry Progress: {batchRetryProgress.mode === 'all-sections' ? 'All Sections' : 'This Section'} · attempt{' '}
                  {batchRetryProgress.attempt} of {batchRetryProgress.maxRetries} ·{' '}
                  {batchRetryProgress.phase === 'preparing'
                    ? 'Preparing retry run'
                    : batchRetryProgress.phase === 'rerender'
                      ? 're-rendering segments'
                      : 're-running audio sync'}
                </div>
                <div>
                  {batchRetryProgress.currentSegmentCount} segment
                  {batchRetryProgress.currentSegmentCount === 1 ? '' : 's'} ·{' '}
                  {batchRetryProgress.currentSectionCount} section
                  {batchRetryProgress.currentSectionCount === 1 ? '' : 's'}
                </div>
              </div>
              <div className="mt-2 h-2 overflow-hidden rounded-full bg-slate-800">
                <div
                  className="h-full rounded-full bg-sky-400 transition-all"
                  style={{
                    width: `${Math.max(
                      8,
                      Math.round(
                        (batchRetryProgress.attempt /
                          Math.max(1, batchRetryProgress.maxRetries)) *
                          100
                      )
                    )}%`,
                  }}
                />
              </div>
            </div>
          )}

          {batchRetryMessage && (
            <div className="mb-3 rounded-md border border-slate-700 bg-slate-900/70 px-3 py-2 text-xs text-slate-300">
              {batchRetryMessage}
            </div>
          )}

          <SseLogPanel jobId={batchValidationRerenderJobId} />
          <SseLogPanel jobId={batchValidationSyncJobId} />

          {flaggedValidationRows.length === 0 ? (
            <div className="text-sm text-slate-400">No flagged transcript mismatches for this section.</div>
          ) : (
            <div className="space-y-3">
              {flaggedValidationRows.map((row) => (
                <div
                  key={row.segmentId}
                  className="rounded-md border border-slate-800 bg-slate-900/80 p-3"
                >
                      <div className="mb-2 flex flex-wrap items-center justify-between gap-3">
                        <div className="text-sm font-medium text-slate-100">
                          {row.segmentId}{' '}
                      <span className="ml-2 text-xs uppercase tracking-wide text-amber-300">
                        {row.status}
                      </span>
                      {typeof row.matchRatio === 'number' && (
                        <span className="ml-2 text-xs text-slate-400">
                          match {(row.matchRatio * 100).toFixed(0)}%
                        </span>
                      )}
                        </div>
                        <div className="flex items-center gap-2">
                          <button
                            onClick={() => handlePreviewSegmentAudio(row.segmentId)}
                            className="rounded-md bg-slate-700 px-3 py-1.5 text-xs font-medium text-white"
                          >
                            {playingSegmentId === row.segmentId ? 'Stop Audio' : 'Play Audio'}
                          </button>
                          <button
                            onClick={() => handleRerenderSegment(row.segmentId)}
                            className="rounded-md bg-amber-600 px-3 py-1.5 text-xs font-medium text-white"
                          >
                            Re-render Segment
                          </button>
                        </div>
                      </div>

                  <div className="grid gap-3 md:grid-cols-2">
                    <div>
                      <div className="mb-1 text-xs font-semibold uppercase tracking-wide text-slate-400">
                        Expected Text
                      </div>
                      <div className="rounded bg-slate-950 px-3 py-2 text-sm text-slate-200">
                        {row.expectedText || 'No expected script found.'}
                      </div>
                    </div>
                    <div>
                      <div className="mb-1 text-xs font-semibold uppercase tracking-wide text-slate-400">
                        Actual Transcript
                      </div>
                      <div className="rounded bg-slate-950 px-3 py-2 text-sm text-slate-200">
                        {row.actualText || 'No speech detected.'}
                      </div>
                    </div>
                  </div>

                  <div className="mt-3">
                    <SseLogPanel
                      jobId={validationJobIds[row.segmentId] ?? null}
                      onDone={() => handleValidationRerenderDone(row.segmentId)}
                    />
                    <SseLogPanel
                      jobId={validationSyncJobIds[row.segmentId] ?? null}
                      onDone={() => handleValidationSyncDone(row.segmentId)}
                    />
                  </div>
                </div>
              ))}
            </div>
          )}
        </div>

        {/* Virtualized Table */}
        <div
          ref={scrollRef}
          onScroll={(e) => setScrollTop(e.currentTarget.scrollTop)}
          className="border border-slate-700 rounded overflow-y-auto"
          style={{ height: VIEWPORT_HEIGHT, contain: 'strict' }}
        >
          <div style={{ height: totalHeight, position: 'relative' }}>
            <div
              style={{
                transform: `translateY(${offsetY}px)`,
              }}
            >
              <table className="w-full text-sm">
                <thead>
                  <tr className="text-left bg-slate-800 text-slate-300 sticky top-0 z-10">
                    <th className="py-2 px-2">Word</th>
                    <th className="py-2 px-2">Start</th>
                    <th className="py-2 px-2">End</th>
                    <th className="py-2 px-2">Segment ID</th>
                  </tr>
                </thead>
                <tbody>
                  {visibleWords.map((w, idx) => (
                    <tr
                      key={`${w.word}-${idx}`}
                      className="border-b border-slate-700 text-slate-200"
                      style={{ height: ROW_HEIGHT }}
                    >
                      <td className="py-1 px-2">{w.word}</td>
                      <td className="py-1 px-2">{w.start.toFixed(3)}</td>
                      <td className="py-1 px-2">{w.end.toFixed(3)}</td>
                      <td className="py-1 px-2">{w.segmentId ?? '-'}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        </div>

        <div className="mt-4 flex justify-end">
          <PipelineAdvanceButton
            onClick={onAdvance}
            label="Continue →"
          />
        </div>
      </div>
    </div>
  );
}
