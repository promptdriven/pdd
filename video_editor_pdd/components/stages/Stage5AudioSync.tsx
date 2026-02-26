'use client';

import React, { useEffect, useMemo, useRef, useState } from 'react';
import type { ProjectConfig, Section } from '../../lib/types';
import SseLogPanel from '../SseLogPanel';

interface Stage5AudioSyncProps {
  onAdvance: () => void;
}

interface WordTimestamp {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
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
  const [loadingTimestamps, setLoadingTimestamps] = useState(false);
  const [search, setSearch] = useState('');

  const [scrollTop, setScrollTop] = useState(0);
  const scrollRef = useRef<HTMLDivElement>(null);

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
            normalized[key] = [sr.startSegment, sr.endSegment].filter(Boolean);
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
      } catch (err) {
        if (!active) return;
        setTimestamps([]);
      } finally {
        if (active) setLoadingTimestamps(false);
      }
    })();
    return () => {
      active = false;
    };
  }, [selectedSectionId]);

  // ----------------------------------------
  // Derived values
  // ----------------------------------------
  const filteredWords = useMemo(() => {
    const term = search.toLowerCase();
    return timestamps.filter((w) => w.word.toLowerCase().includes(term));
  }, [timestamps, search]);

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

  const handleSaveConfig = async () => {
    setSavingConfig(true);
    try {
      await fetch('/api/project', {
        method: 'PUT',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          audioSync: { sectionGroups },
        }),
      });
    } finally {
      setSavingConfig(false);
    }
  };

  const handleRunAudioSync = async () => {
    const res = await fetch('/api/pipeline/audio-sync/run', {
      method: 'POST',
    });
    const data = await res.json();
    setJobId(data.jobId);
  };

  const handleSseDone = () => {
    // Auto-load timestamps for first section after run completes
    if (project?.sections?.length && !selectedSectionId) {
      setSelectedSectionId(project.sections[0].id);
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
                <td className="py-2 pr-4 font-medium text-slate-200">{section.label}</td>
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

        <div className="mt-4">
          <SseLogPanel jobId={jobId} onDone={handleSseDone} />
        </div>
      </div>

      {/* Bottom Section: Word Timestamp Viewer */}
      <div className="rounded-lg border border-slate-700 bg-slate-900 p-4 shadow-sm">
        <div className="flex flex-wrap items-center gap-4 mb-4">
          <h2 className="text-lg font-semibold text-slate-100">Word Timestamp Viewer</h2>

          <div className="flex items-center gap-2">
            <label className="text-sm text-slate-300">Section:</label>
            <select
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
          <button
            onClick={onAdvance}
            className="rounded-md bg-slate-700 px-4 py-2 text-white text-sm hover:bg-slate-600"
          >
            Continue
          </button>
        </div>
      </div>
    </div>
  );
}