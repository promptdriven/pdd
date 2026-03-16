'use client';

import React, { useEffect, useMemo, useRef, useState } from 'react';
import type { ProjectConfig, Section } from '../../lib/types';
import PipelineAdvanceButton from '../PipelineAdvanceButton';
import SseLogPanel from '../SseLogPanel';
import { extractJobIdFromSse } from '@/lib/client/sse-utils';

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

const EMPTY_VALIDATION_SUMMARY: SegmentValidationSummary = {
  passCount: 0,
  warnCount: 0,
  failCount: 0,
  skipCount: 0,
};

function expandRange(start: string, end: string): string[] {
  const sm = start.match(/^(.+)_(\d{3})$/);
  const em = end.match(/^(.+)_(\d{3})$/);
  if (!sm || !em || sm[1] !== em[1]) return [start, end].filter(Boolean);
  const prefix = sm[1];
  const s = parseInt(sm[2], 10);
  const e = parseInt(em[2], 10);
  const result: string[] = [];
  for (let i = s; i <= e; i++) {
    result.push(`${prefix}_${String(i).padStart(3, '0')}`);
  }
  return result;
}

const ROW_HEIGHT = 32;
const VIEWPORT_HEIGHT = 320;

export default function Stage5AudioSync({ onAdvance }: Stage5AudioSyncProps) {
  const [project, setProject] = useState<ProjectConfig | null>(null);
  const [loadingProject, setLoadingProject] = useState(true);
  const [projectError, setProjectError] = useState<string | null>(null);

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
  const [loadingTimestamps, setLoadingTimestamps] = useState(false);
  const [search, setSearch] = useState('');
  const [validationJobIds, setValidationJobIds] = useState<Record<string, string | null>>({});
  const [validationSyncJobIds, setValidationSyncJobIds] = useState<Record<string, string | null>>({});
  const [dataReloadVersion, setDataReloadVersion] = useState(0);
  const [playingSegmentId, setPlayingSegmentId] = useState<string | null>(null);

  const [scrollTop, setScrollTop] = useState(0);
  const scrollRef = useRef<HTMLDivElement>(null);
  const previewAudioRef = useRef<HTMLAudioElement | null>(null);

  const [detecting, setDetecting] = useState(false);
  const [detectError, setDetectError] = useState<string | null>(null);
  const [unmatchedSegments, setUnmatchedSegments] = useState<string[]>([]);
  const [overwriteExisting, setOverwriteExisting] = useState(false);
  const [autoFilledSections, setAutoFilledSections] = useState<string[]>([]);

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
        // Normalize sectionGroups: API may return SegmentRange objects
        // ({ startSegment, endSegment }) or string arrays.
        const rawGroups = data.audioSync?.sectionGroups ?? {};
        const normalized: Record<string, string[]> = {};
        for (const [key, val] of Object.entries(rawGroups)) {
          if (Array.isArray(val)) {
            normalized[key] = val;
          } else if (val && typeof val === 'object' && 'startSegment' in val) {
            const sr = val as { startSegment: string; endSegment: string };
            normalized[key] = expandRange(sr.startSegment, sr.endSegment);
          } else {
            normalized[key] = [];
          }
        }
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
      try {
        setLoadingTimestamps(true);
        const res = await fetch(
          `/api/pipeline/audio-sync/timestamps?section=${encodeURIComponent(
            selectedSectionId
          )}`
        );
        if (!res.ok) {
          if (!active) return;
          setTimestamps([]);
          return;
        }
        const data = await res.json();
        if (!active) return;
        // API returns { words: [...] } or a raw array
        const list = Array.isArray(data) ? data : (Array.isArray(data?.words) ? data.words : []);
        setTimestamps(list);
        setValidationRows(Array.isArray(data?.validation?.segments) ? data.validation.segments : []);
        setValidationSummary(data?.validation?.summary ?? EMPTY_VALIDATION_SUMMARY);
      } catch (err) {
        if (!active) return;
        setTimestamps([]);
        setValidationRows([]);
        setValidationSummary(EMPTY_VALIDATION_SUMMARY);
      } finally {
        if (active) setLoadingTimestamps(false);
      }
    })();
    return () => {
      active = false;
    };
  }, [dataReloadVersion, selectedSectionId]);

  useEffect(() => {
    return () => {
      if (previewAudioRef.current) {
        previewAudioRef.current.pause();
        previewAudioRef.current = null;
      }
    };
  }, []);

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

      const grouped: Record<string, string[]> = {};
      const unmatched: string[] = [];

      for (const seg of allSegments) {
        let matched = false;
        let prefixMatched = false;
        for (const sectionId of sortedSectionIds) {
          const prefix = sectionId + '_';
          if (seg.id.startsWith(prefix)) {
            prefixMatched = true;
            const suffix = seg.id.slice(prefix.length);
            if (/^\d{3}$/.test(suffix)) {
              if (!grouped[sectionId]) grouped[sectionId] = [];
              grouped[sectionId].push(seg.id);
              matched = true;
              break;
            }
          }
        }
        if (!matched && prefixMatched) unmatched.push(seg.id);
      }

      setUnmatchedSegments(unmatched);

      const filled: string[] = [];
      setSectionGroups((prev) => {
        const next = { ...prev };
        for (const [sectionId, segments] of Object.entries(grouped)) {
          const existing = prev[sectionId] ?? [];
          if (existing.length === 0 || overwriteExisting) {
            next[sectionId] = segments.sort();
            filled.push(sectionId);
          }
        }
        return next;
      });

      setAutoFilledSections(filled);
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
      // Convert string[] arrays to {startSegment, endSegment} SegmentRange objects
      const rangeGroups: Record<string, { startSegment: string; endSegment: string }> = {};
      for (const [sectionId, segments] of Object.entries(sectionGroups)) {
        if (segments.length > 0) {
          rangeGroups[sectionId] = {
            startSegment: segments[0],
            endSegment: segments[segments.length - 1],
          };
        }
      }
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
        body: JSON.stringify({ segments: [segmentId] }),
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
        body: JSON.stringify({ sections: [selectedSectionId] }),
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

  const handlePreviewSegmentAudio = async (segmentId: string) => {
    try {
      if (playingSegmentId === segmentId) {
        previewAudioRef.current?.pause();
        previewAudioRef.current = null;
        setPlayingSegmentId(null);
        return;
      }

      if (previewAudioRef.current) {
        previewAudioRef.current.pause();
        previewAudioRef.current = null;
      }

      const audio = new Audio(`/api/audio/tts/${segmentId}.wav?v=${Date.now()}`);
      audio.addEventListener('ended', () => {
        if (previewAudioRef.current === audio) {
          previewAudioRef.current = null;
          setPlayingSegmentId(null);
        }
      });
      previewAudioRef.current = audio;
      await audio.play();
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

  const sections: Section[] = project?.sections ?? [];

  return (
    <div className="space-y-6">
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
