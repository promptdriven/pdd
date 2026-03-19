'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import ReactMarkdown from 'react-markdown';
import PipelineAdvanceButton from '../PipelineAdvanceButton';

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
  const [renderMenuOpen, setRenderMenuOpen] = useState(false);
  const [renderJobId, setRenderJobId] = useState<string | null>(null);
  const [loadingStatus, setLoadingStatus] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [stitching, setStitching] = useState(false);

  const [previewSectionId, setPreviewSectionId] = useState<string | null>(null);
  const [previewScriptContent, setPreviewScriptContent] = useState<string | null>(null);
  const [previewScriptHeading, setPreviewScriptHeading] = useState<string | null>(null);
  const [previewScriptLoading, setPreviewScriptLoading] = useState(false);
  const [previewScriptError, setPreviewScriptError] = useState<string | null>(null);

  const eventSourceRef = useRef<EventSource | null>(null);
  const renderMenuRef = useRef<HTMLDivElement | null>(null);

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

  useEffect(() => {
    if (!renderMenuOpen) return;

    const handlePointerDown = (event: MouseEvent) => {
      const target = event.target;
      if (
        renderMenuRef.current &&
        target instanceof Node &&
        !renderMenuRef.current.contains(target)
      ) {
        setRenderMenuOpen(false);
      }
    };

    document.addEventListener('mousedown', handlePointerDown);
    return () => document.removeEventListener('mousedown', handlePointerDown);
  }, [renderMenuOpen]);

  useEffect(() => {
    if (!previewSectionId) {
      setPreviewScriptContent(null);
      setPreviewScriptHeading(null);
      setPreviewScriptLoading(false);
      setPreviewScriptError(null);
      return;
    }

    let cancelled = false;
    setPreviewScriptLoading(true);
    setPreviewScriptError(null);

    const loadPreviewScript = async () => {
      try {
        const res = await fetch(
          `/api/project/script?file=main&section=${encodeURIComponent(previewSectionId)}`
        );
        if (!res.ok) {
          throw new Error('Failed to load section script.');
        }
        const data = await res.json();
        if (cancelled) return;
        setPreviewScriptHeading(data.sectionHeading ?? null);
        setPreviewScriptContent(data.sectionContent ?? data.content ?? '');
      } catch (err: any) {
        if (cancelled) return;
        setPreviewScriptHeading(null);
        setPreviewScriptContent(null);
        setPreviewScriptError(err?.message || 'Failed to load section script.');
      } finally {
        if (!cancelled) {
          setPreviewScriptLoading(false);
        }
      }
    };

    void loadPreviewScript();

    return () => {
      cancelled = true;
    };
  }, [previewSectionId]);

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

  const handleRenderSelection = async (mode: RenderMode) => {
    setRenderMenuOpen(false);
    await handleRender(mode);
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
          <div className="relative" ref={renderMenuRef}>
            <button
              data-testid="render-sections-button"
              type="button"
              aria-haspopup="menu"
              aria-expanded={renderMenuOpen}
              onClick={() => setRenderMenuOpen((prev) => !prev)}
              className="px-4 py-2 bg-blue-600 text-white rounded-md text-sm font-medium hover:bg-blue-700"
            >
              Render ▾
            </button>
            {renderMenuOpen && (
              <div
                className="absolute right-0 z-10 mt-2 min-w-[12rem] overflow-hidden rounded-md border border-slate-600 bg-slate-800 shadow-lg"
                role="menu"
              >
                <button
                  type="button"
                  role="menuitem"
                  className="block w-full px-4 py-2 text-left text-sm text-slate-200 hover:bg-slate-700"
                  onClick={() => void handleRenderSelection('all')}
                >
                  Render All
                </button>
                <button
                  type="button"
                  role="menuitem"
                  className="block w-full px-4 py-2 text-left text-sm text-slate-200 hover:bg-slate-700"
                  onClick={() => void handleRenderSelection('missing')}
                >
                  Render Missing
                </button>
                <button
                  type="button"
                  role="menuitem"
                  className="block w-full px-4 py-2 text-left text-sm text-slate-200 hover:bg-slate-700"
                  onClick={() => void handleRenderSelection('selected')}
                >
                  Render Selected
                </button>
              </div>
            )}
          </div>
          <button
            data-testid="stitch-full-video-button"
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
          <PipelineAdvanceButton
            onClick={onAdvance}
            label="Continue →"
          />
        </div>
      )}

      {/* Preview Modal */}
      {previewSectionId && (
        <div
          className="fixed inset-0 z-50 flex items-center justify-center overflow-hidden bg-black/50 p-4"
          onClick={() => setPreviewSectionId(null)}
        >
          <div
            className="flex w-full min-h-0 flex-col overflow-hidden rounded-lg bg-slate-900 p-4"
            style={{ height: '90vh', maxWidth: '80rem' }}
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
            <div
              className="grid min-h-0 flex-1 min-w-0 gap-4"
              style={{ gridTemplateColumns: '20rem minmax(0, 1fr)' }}
            >
              <div className="min-h-0 min-w-0 overflow-hidden rounded-md border border-slate-700 bg-slate-950/70">
                <div className="flex h-full min-h-0 flex-col">
                <div className="border-b border-slate-800 px-4 py-3">
                  <div className="text-sm font-semibold text-slate-100">Original Script</div>
                  <div className="text-xs text-slate-400">
                    {previewScriptHeading ?? previewSectionId}
                  </div>
                </div>
                <div className="min-h-0 flex-1 overflow-y-auto px-4 py-3">
                  {previewScriptLoading ? (
                    <div className="text-sm text-slate-400">Loading script...</div>
                  ) : previewScriptError ? (
                    <div className="text-sm text-red-300">{previewScriptError}</div>
                  ) : (
                    <div className="text-xs text-slate-200">
                      <ReactMarkdown
                        components={{
                          h1: ({ children }) => <h1 className="text-base font-bold text-slate-100 mt-4 mb-2">{children}</h1>,
                          h2: ({ children }) => <h2 className="text-sm font-bold text-slate-100 mt-4 mb-2">{children}</h2>,
                          h3: ({ children }) => <h3 className="text-xs font-bold text-slate-100 mt-3 mb-1">{children}</h3>,
                          p: ({ children }) => <p className="mb-3 leading-6">{children}</p>,
                          strong: ({ children }) => <strong className="font-bold text-slate-100">{children}</strong>,
                          em: ({ children }) => <em className="italic text-slate-300">{children}</em>,
                          ul: ({ children }) => <ul className="list-disc pl-4 mb-3">{children}</ul>,
                          ol: ({ children }) => <ol className="list-decimal pl-4 mb-3">{children}</ol>,
                          li: ({ children }) => <li className="mb-1">{children}</li>,
                          blockquote: ({ children }) => <blockquote className="border-l-2 border-slate-600 pl-3 italic text-slate-400 mb-3">{children}</blockquote>,
                          hr: () => <hr className="border-slate-700 my-4" />,
                        }}
                      >
                        {previewScriptContent || 'Script content not available.'}
                      </ReactMarkdown>
                    </div>
                  )}
                </div>
                </div>
              </div>
              <div className="min-w-0">
                <div className="flex h-full items-center justify-center rounded-md bg-slate-950/70 p-2">
                  <video
                    src={`/api/video/outputs/sections/${previewSectionId}.mp4`}
                    controls
                    className="max-h-full w-full max-w-full rounded bg-black object-contain"
                  />
                </div>
              </div>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
