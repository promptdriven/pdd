'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';

interface SectionRenderStatus {
  id: string;
  durationSeconds: number;
  status: 'missing' | 'rendering' | 'done' | 'error';
  progress: number; // 0 - 100
}

interface FullVideoInfo {
  exists: boolean;
  sizeBytes?: number;
  durationSeconds?: number;
}

interface RenderStatusResponse {
  sections: SectionRenderStatus[];
  fullVideo: FullVideoInfo;
}

interface Stage9RenderStitchProps {
  onAdvance: () => void;
}

type RenderMode = 'all' | 'missing' | 'selected';

export default function Stage9RenderStitch({ onAdvance }: Stage9RenderStitchProps) {
  const [sections, setSections] = useState<SectionRenderStatus[]>([]);
  const [fullVideo, setFullVideo] = useState<FullVideoInfo>({ exists: false });
  const [selected, setSelected] = useState<Record<string, boolean>>({});
  const [renderMode, setRenderMode] = useState<RenderMode>('all');
  const [renderJobId, setRenderJobId] = useState<string | null>(null);
  const [loadingStatus, setLoadingStatus] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [stitching, setStitching] = useState(false);

  const [previewSectionId, setPreviewSectionId] = useState<string | null>(null);

  const eventSourceRef = useRef<EventSource | null>(null);

  const loadStatus = useCallback(async () => {
    setLoadingStatus(true);
    setError(null);
    try {
      const res = await fetch('/api/pipeline/render/status');
      if (!res.ok) throw new Error('Failed to load render status.');
      const data: RenderStatusResponse = await res.json();
      setSections(data.sections || []);
      setFullVideo(data.fullVideo || { exists: false });
    } catch (err: any) {
      setError(err?.message || 'Unable to load render status.');
    } finally {
      setLoadingStatus(false);
    }
  }, []);

  useEffect(() => {
    loadStatus();
  }, [loadStatus]);

  // SSE: stream render progress for active job
  useEffect(() => {
    if (!renderJobId) return;

    eventSourceRef.current?.close();
    const es = new EventSource(`/api/pipeline/render/stream?jobId=${renderJobId}`);
    eventSourceRef.current = es;

    const handleMessage = (event: MessageEvent) => {
      try {
        const data = JSON.parse(event.data);
        if (data?.type === 'section-progress') {
          const { sectionId, percent } = data as { sectionId: string; percent: number };
          setSections((prev) =>
            prev.map((s) =>
              s.id === sectionId
                ? {
                    ...s,
                    progress: Math.max(0, Math.min(100, Math.round(percent))),
                    status: percent >= 100 ? 'done' : 'rendering',
                  }
                : s
            )
          );
        }
        if (data?.type === 'render-complete') {
          setRenderJobId(null);
          loadStatus();
        }
        if (data?.type === 'render-error') {
          setRenderJobId(null);
          loadStatus();
        }
      } catch (e) {
        // ignore parse errors
      }
    };

    es.addEventListener('message', handleMessage);
    es.addEventListener('error', () => {
      // connection failed; polling handled by loadStatus
    });

    return () => {
      es.close();
    };
  }, [renderJobId, loadStatus]);

  const activeRenders = useMemo(
    () => sections.filter((s) => s.progress > 0 && s.progress < 100).slice(0, 3),
    [sections]
  );

  const anyRenderInProgress = useMemo(
    () => sections.some((s) => s.progress > 0 && s.progress < 100),
    [sections]
  );

  const handleRender = async (mode: RenderMode) => {
    setError(null);
    let toRender: string[] = [];

    if (mode === 'all') {
      toRender = sections.map((s) => s.id);
    } else if (mode === 'missing') {
      toRender = sections
        .filter((s) => s.status === 'missing' || s.progress === 0)
        .map((s) => s.id);
    } else if (mode === 'selected') {
      toRender = Object.keys(selected).filter((id) => selected[id]);
    }

    if (toRender.length === 0) {
      setError('No sections selected for render.');
      return;
    }

    try {
      const res = await fetch('/api/pipeline/render/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ sections: toRender }),
      });
      if (!res.ok) throw new Error('Failed to start render job.');
      const data = await res.json();
      if (data?.jobId) setRenderJobId(data.jobId);
      await loadStatus();
    } catch (err: any) {
      setError(err?.message || 'Failed to start render job.');
    }
  };

  const handleRerenderSection = async (sectionId: string) => {
    setSelected((prev) => ({ ...prev, [sectionId]: true }));
    setError(null);
    try {
      const res = await fetch('/api/pipeline/render/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ sections: [sectionId] }),
      });
      if (!res.ok) throw new Error('Failed to start render job.');
      const data = await res.json();
      if (data?.jobId) setRenderJobId(data.jobId);
      await loadStatus();
    } catch (err: any) {
      setError(err?.message || 'Failed to start render job.');
    }
  };

  const handleStitch = async () => {
    setError(null);
    setStitching(true);
    try {
      const res = await fetch('/api/pipeline/stitch/run', { method: 'POST' });
      if (!res.ok) throw new Error('Failed to stitch full video.');
      await loadStatus();
    } catch (err: any) {
      setError(err?.message || 'Failed to stitch full video.');
    } finally {
      setStitching(false);
    }
  };

  const formatBytes = (bytes?: number) => {
    if (!bytes || bytes <= 0) return '—';
    const gb = 1024 ** 3;
    const mb = 1024 ** 2;
    if (bytes >= gb) return `${(bytes / gb).toFixed(2)} GB`;
    return `${(bytes / mb).toFixed(2)} MB`;
  };

  const statusBadge = (status: SectionRenderStatus['status']) => {
    const color =
      status === 'done'
        ? 'bg-green-900/50 text-green-300'
        : status === 'rendering'
        ? 'bg-blue-900/50 text-blue-300'
        : status === 'error'
        ? 'bg-red-900/50 text-red-300'
        : 'bg-yellow-900/50 text-yellow-300';

    const label =
      status === 'done'
        ? 'Rendered'
        : status === 'rendering'
        ? 'Rendering'
        : status === 'error'
        ? 'Error'
        : 'Missing';

    return (
      <span className={`px-2 py-1 rounded-full text-xs font-medium ${color}`}>
        {label}
      </span>
    );
  };

  return (
    <div className="space-y-6">
      <div className="flex flex-wrap items-center justify-between gap-3">
        <div>
          <h2 className="text-xl font-semibold text-white">Stage 9 — Render &amp; Stitch</h2>
          <p className="text-sm text-slate-300">
            Render Remotion sections in parallel, then stitch into the full video.
          </p>
        </div>

        <div className="flex items-center gap-2">
          <select
            className="border rounded-md px-3 py-2 text-sm text-slate-200 bg-slate-800 border-slate-600"
            value={renderMode}
            onChange={(e) => setRenderMode(e.target.value as RenderMode)}
          >
            <option value="all">All</option>
            <option value="missing">Missing</option>
            <option value="selected">Selected</option>
          </select>
          <button
            onClick={() => handleRender(renderMode)}
            className="px-4 py-2 bg-blue-600 text-white rounded-md text-sm font-medium hover:bg-blue-700"
          >
            Render ▾
          </button>
          <button
            onClick={handleStitch}
            disabled={anyRenderInProgress || stitching}
            className={`px-4 py-2 rounded-md text-sm font-medium ${
              anyRenderInProgress || stitching
                ? 'bg-slate-700 text-slate-400 cursor-not-allowed'
                : 'bg-emerald-600 text-white hover:bg-emerald-700'
            }`}
          >
            Stitch Full Video
          </button>
        </div>
      </div>

      {error && (
        <div className="p-3 rounded-md bg-red-900/50 text-red-300 text-sm">{error}</div>
      )}

      {/* Active renders panel */}
      {activeRenders.length > 0 && (
        <div className="bg-slate-900 rounded-lg shadow-sm p-4 border border-slate-700">
          <h3 className="text-sm font-semibold text-slate-200 mb-3">
            Active Renders
          </h3>
          <div className="space-y-3">
            {activeRenders.map((s) => (
              <div key={s.id}>
                <div className="text-xs text-slate-300 mb-1">
                  Section: <span className="font-medium">{s.id}</span>
                </div>
                <div className="h-2 bg-slate-700 rounded">
                  <div
                    className="h-2 bg-green-400 transition-all"
                    style={{ width: `${s.progress}%` }}
                  />
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* Section render table */}
      <div className="bg-slate-900 rounded-lg shadow-sm border border-slate-700">
        <div className="px-4 py-3 border-b flex items-center justify-between">
          <h3 className="text-sm font-semibold text-slate-200">Section Renders</h3>
          {loadingStatus && <span className="text-xs text-slate-400">Loading...</span>}
        </div>
        <table className="w-full text-sm text-slate-200">
          <thead className="bg-slate-800 text-slate-300">
            <tr>
              <th className="px-4 py-2 text-left">Select</th>
              <th className="px-4 py-2 text-left">Section ID</th>
              <th className="px-4 py-2 text-left">Duration (s)</th>
              <th className="px-4 py-2 text-left">Status</th>
              <th className="px-4 py-2 text-left">Progress</th>
              <th className="px-4 py-2 text-left">Preview</th>
              <th className="px-4 py-2 text-left">Re-render</th>
            </tr>
          </thead>
          <tbody>
            {sections.map((s) => (
              <tr key={s.id} className="border-t">
                <td className="px-4 py-2">
                  <input
                    type="checkbox"
                    checked={!!selected[s.id]}
                    onChange={(e) =>
                      setSelected((prev) => ({ ...prev, [s.id]: e.target.checked }))
                    }
                  />
                </td>
                <td className="px-4 py-2 font-mono text-slate-200">{s.id}</td>
                <td className="px-4 py-2 text-slate-200">{s.durationSeconds.toFixed(2)}</td>
                <td className="px-4 py-2">{statusBadge(s.status)}</td>
                <td className="px-4 py-2">
                  <div className="h-2 bg-slate-700 rounded">
                    <div
                      className="h-2 bg-green-400 transition-all"
                      style={{ width: `${s.progress}%` }}
                    />
                  </div>
                  <div className="text-xs text-slate-400 mt-1">{s.progress}%</div>
                </td>
                <td className="px-4 py-2">
                  <button
                    onClick={() => setPreviewSectionId(s.id)}
                    disabled={s.status === 'missing'}
                    className={
                      s.status === 'missing'
                        ? 'text-slate-600 cursor-not-allowed'
                        : 'text-blue-600 hover:text-blue-700'
                    }
                    title={s.status === 'missing' ? 'Not yet rendered' : 'Preview'}
                  >
                    ▶
                  </button>
                </td>
                <td className="px-4 py-2">
                  <button
                    onClick={() => handleRerenderSection(s.id)}
                    className="text-slate-300 hover:text-slate-100"
                    title="Re-render"
                  >
                    ↺
                  </button>
                </td>
              </tr>
            ))}
            {sections.length === 0 && (
              <tr>
                <td colSpan={7} className="px-4 py-6 text-center text-slate-400">
                  No sections found.
                </td>
              </tr>
            )}
          </tbody>
        </table>
      </div>

      {/* Full video panel */}
      {fullVideo.exists && (
        <div className="bg-slate-900 rounded-lg shadow-sm p-4 border border-slate-700 flex items-center justify-between">
          <div>
            <div className="text-sm font-semibold text-slate-200">Full Video</div>
            <div className="text-xs text-slate-400">
              Size: {formatBytes(fullVideo.sizeBytes)} • Duration:{' '}
              {fullVideo.durationSeconds?.toFixed(2) ?? '—'}s
            </div>
          </div>
          <button
            onClick={onAdvance}
            className="px-4 py-2 bg-indigo-600 text-white rounded-md text-sm font-medium hover:bg-indigo-700"
          >
            Open in Review →
          </button>
        </div>
      )}

      {/* Preview Modal */}
      {previewSectionId && (
        <div
          className="fixed inset-0 bg-black/50 z-50 flex items-center justify-center p-4"
          onClick={() => setPreviewSectionId(null)}
        >
          <div
            className="bg-slate-900 rounded-lg p-4 max-w-3xl w-full"
            onClick={(e) => e.stopPropagation()}
          >
            <div className="flex items-center justify-between mb-3">
              <div className="font-medium text-slate-200">
                Preview — {previewSectionId}
              </div>
              <button
                onClick={() => setPreviewSectionId(null)}
                className="text-slate-400 hover:text-slate-200"
              >
                ✕
              </button>
            </div>
            <video
              src={`/api/video/outputs/sections/${previewSectionId}.mp4`}
              controls
              className="max-w-full w-full rounded"
            />
          </div>
        </div>
      )}
    </div>
  );
}