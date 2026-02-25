'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import WaveSurfer from 'wavesurfer.js';
import { SseLogPanel } from '../SseLogPanel';

type SegmentStatus = 'done' | 'missing' | 'error' | 'generating';

interface TtsSegment {
  id: string;
  status: SegmentStatus;
  text: string;
}

interface Stage4TtsRenderingProps {
  onAdvance: () => void;
}

interface BatchProgress {
  currentSegment: string | null;
  completedCount: number;
  total: number;
  percent: number;
}

const defaultProgress: BatchProgress = {
  currentSegment: null,
  completedCount: 0,
  total: 0,
  percent: 0,
};

/**
 * Stage4TtsRendering component handles the generation and preview of TTS audio segments.
 * It supports batch processing, individual re-renders, and visualizes audio waveforms.
 */
export default function Stage4TtsRendering({ onAdvance }: Stage4TtsRenderingProps) {
  const [segments, setSegments] = useState<TtsSegment[]>([]);
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);

  const [expandedId, setExpandedId] = useState<string | null>(null);
  const [batchJobId, setBatchJobId] = useState<string | null>(null);
  const [batchProgress, setBatchProgress] = useState<BatchProgress>(defaultProgress);

  // Per-row re-render jobs tracking
  const [rowJobIds, setRowJobIds] = useState<Record<string, string | null>>({});

  const waveformRefs = useRef<Map<string, HTMLDivElement | null>>(new Map());
  const wavesurferMap = useRef<Map<string, WaveSurfer>>(new Map());
  const batchEventSource = useRef<EventSource | null>(null);

  const allDone = useMemo(() => segments.length > 0 && segments.every((s) => s.status === 'done'), [segments]);

  const fetchSegments = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const res = await fetch('/api/pipeline/tts-render/segments');
      if (!res.ok) throw new Error('Failed to load TTS segments.');
      const data = await res.json();
      const list: TtsSegment[] = Array.isArray(data) ? data : (data.segments ?? []);
      setSegments(list);
    } catch (err: any) {
      setError(err.message || 'Failed to load TTS segments.');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    fetchSegments();
  }, [fetchSegments]);

  // Initialize WaveSurfer on expand
  useEffect(() => {
    if (!expandedId) return;
    if (wavesurferMap.current.has(expandedId)) return;
    const container = waveformRefs.current.get(expandedId);
    if (!container) return;

    const ws = WaveSurfer.create({
      container,
      url: `/api/audio/tts/${expandedId}.wav`,
      height: 64,
      waveColor: '#4ade80',
      progressColor: '#166534',
    });

    wavesurferMap.current.set(expandedId, ws);

    // Auto-play if this expand was triggered by the Play button
    if (pendingPlayRef.current === expandedId) {
      ws.once('ready', () => {
        ws.play();
      });
      pendingPlayRef.current = null;
    }

    return () => {
      // Keep instance cached for reuse or cleanup if necessary
    };
  }, [expandedId]);

  // Cleanup on unmount
  useEffect(() => {
    return () => {
      batchEventSource.current?.close();
      wavesurferMap.current.forEach((ws) => ws.destroy());
      wavesurferMap.current.clear();
    };
  }, []);

  const pendingPlayRef = useRef<string | null>(null);

  const handlePlay = (id: string) => {
    const ws = wavesurferMap.current.get(id);
    if (ws) {
      ws.playPause();
    } else {
      // Auto-expand the row so WaveSurfer initializes, then play once ready
      pendingPlayRef.current = id;
      setExpandedId(id);
    }
  };

  const handleRowToggle = (id: string) => {
    setExpandedId((prev) => (prev === id ? null : id));
  };

  const startBatchRender = async (segmentsFilter?: string[]) => {
    setBatchProgress(defaultProgress);
    setBatchJobId(null);

    try {
      const res = await fetch('/api/pipeline/tts-render/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: segmentsFilter ? JSON.stringify({ segments: segmentsFilter }) : undefined,
      });

      if (!res.ok) throw new Error('Failed to start TTS render.');
      const data = await res.json();

      const jobId = data.jobId as string;
      setBatchJobId(jobId);

      // Open SSE stream for batch progress
      batchEventSource.current?.close();
      const es = new EventSource(`/api/jobs/${jobId}/stream`);
      batchEventSource.current = es;

      es.addEventListener('message', (event) => {
        try {
          const payload = JSON.parse(event.data);
          // Expected: { type: 'segment', segmentId, status, completedCount, total }
          if (payload.type === 'segment') {
            setSegments((prev) =>
              prev.map((s) =>
                s.id === payload.segmentId
                  ? { ...s, status: payload.status as SegmentStatus }
                  : s
              )
            );

            setBatchProgress((prev) => {
              const completed = payload.completedCount ?? prev.completedCount;
              const total = payload.total ?? prev.total;
              const percent =
                total && completed ? Math.round((completed / total) * 100) : prev.percent;

              return {
                currentSegment: payload.segmentId ?? prev.currentSegment,
                completedCount: completed,
                total,
                percent,
              };
            });
          }
        } catch (err) {
          // Ignore parse errors
        }
      });

      es.addEventListener('done', () => {
        batchEventSource.current?.close();
        setBatchJobId(null);
        fetchSegments();
      });

      es.addEventListener('error', () => {
        batchEventSource.current?.close();
      });
    } catch (err: any) {
      setError(err.message || 'Failed to start TTS render.');
    }
  };

  const handleRenderAll = () => startBatchRender();
  const handleRenderMissing = () => {
    const missing = segments.filter((s) => s.status !== 'done').map((s) => s.id);
    startBatchRender(missing);
  };

  const handleRowRerender = async (segmentId: string) => {
    try {
      const res = await fetch('/api/pipeline/tts-render/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ segments: [segmentId] }),
      });
      if (!res.ok) throw new Error('Failed to start segment render.');
      const data = await res.json();
      const jobId = data.jobId as string;

      setRowJobIds((prev) => ({ ...prev, [segmentId]: jobId }));
    } catch (err: any) {
      setError(err.message || 'Failed to start segment render.');
    }
  };

  const renderStatusBadge = (status: SegmentStatus) => {
    const base = 'px-2 py-1 text-xs rounded font-semibold';
    if (status === 'done') return <span className={`${base} bg-green-900/50 text-green-400`}>done</span>;
    if (status === 'generating') return <span className={`${base} bg-amber-900/50 text-amber-400 animate-pulse`}>generating</span>;
    if (status === 'error') return <span className={`${base} bg-red-900/50 text-red-400`}>error</span>;
    return <span className={`${base} bg-yellow-900/50 text-yellow-400`}>missing</span>;
  };

  return (
    <div className="p-6 space-y-6">
      <h2 className="text-xl font-semibold">Stage 4 — TTS Rendering</h2>
      {/* Toolbar */}
      <div className="flex items-center justify-between gap-4">
        <div className="flex gap-3">
          <button
            onClick={handleRenderAll}
            className="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700"
          >
            Render All
          </button>
          <button
            onClick={handleRenderMissing}
            className="px-4 py-2 bg-slate-700 text-white rounded-lg hover:bg-slate-800"
          >
            Render Missing
          </button>
        </div>

        <button
          disabled={!allDone}
          onClick={onAdvance}
          className={`px-4 py-2 rounded-lg font-semibold ${
            allDone ? 'bg-emerald-600 text-white hover:bg-emerald-700' : 'bg-slate-700 text-slate-500'
          }`}
        >
          Advance →
        </button>
      </div>

      {/* Batch progress bar */}
      {batchJobId && (
        <div className="bg-slate-800 p-4 rounded-lg shadow border border-slate-700">
          <div className="text-sm text-slate-300 mb-2">
            Rendering segment: <strong>{batchProgress.currentSegment ?? '...'}</strong>
          </div>
          <div className="w-full h-3 bg-slate-700 rounded-full overflow-hidden">
            <div
              className="h-full bg-emerald-500 transition-all"
              style={{ width: `${batchProgress.percent}%` }}
            />
          </div>
          <div className="text-xs text-slate-400 mt-2">
            {batchProgress.completedCount}/{batchProgress.total} ({batchProgress.percent}%)
          </div>
        </div>
      )}

      {/* Error */}
      {error && (
        <div className="bg-red-900/30 border border-red-700 text-red-400 p-3 rounded">
          {error}
        </div>
      )}

      {/* Table */}
      <div className="bg-slate-800 rounded-lg shadow border border-slate-700 overflow-hidden">
        <div className="grid grid-cols-6 px-4 py-2 bg-slate-700 text-xs font-semibold text-slate-300">
          <div>#</div>
          <div>Segment ID</div>
          <div>Status</div>
          <div>Play</div>
          <div>Re-render</div>
          <div></div>
        </div>

        {loading && (
          <div className="p-4 text-sm text-slate-400">Loading segments...</div>
        )}

        {!loading && segments.length === 0 && (
          <div className="p-4 text-sm text-slate-400">No segments found.</div>
        )}

        {segments.map((seg, idx) => {
          const isExpanded = expandedId === seg.id;
          return (
            <div key={`${seg.id}-${idx}`} className="border-t border-slate-700">
              <div
                className="grid grid-cols-6 px-4 py-3 items-center hover:bg-slate-700/50 cursor-pointer"
                onClick={() => handleRowToggle(seg.id)}
              >
                <div className="text-sm text-slate-200">{idx + 1}</div>
                <div className="text-sm font-mono text-slate-200">{seg.id}</div>
                <div>{renderStatusBadge(seg.status)}</div>
                <div>
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      handlePlay(seg.id);
                    }}
                    className="px-2 py-1 bg-slate-600 rounded hover:bg-slate-500 text-xs text-slate-200"
                  >
                    ▶
                  </button>
                </div>
                <div>
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      handleRowRerender(seg.id);
                    }}
                    className="px-2 py-1 bg-slate-600 rounded hover:bg-slate-500 text-xs text-slate-200"
                  >
                    ↺
                  </button>
                </div>
                <div className="text-right text-xs text-slate-400">
                  {isExpanded ? '▲' : '▼'}
                </div>
              </div>

              {isExpanded && (
                <div className="px-4 pb-4">
                  <div
                    className="w-full rounded bg-slate-900 p-2"
                    ref={(el) => { waveformRefs.current.set(seg.id, el); }}
                  />
                  <div className="mt-2 text-sm text-slate-300 whitespace-pre-line">
                    {seg.text}
                  </div>

                  {rowJobIds[seg.id] && (
                    <div className="mt-3">
                      <SseLogPanel
                        jobId={rowJobIds[seg.id] ?? null}
                        onDone={() => {
                          setRowJobIds((prev) => ({ ...prev, [seg.id]: null }));
                          fetchSegments();
                        }}
                        onError={() => {
                          setRowJobIds((prev) => ({ ...prev, [seg.id]: null }));
                          fetchSegments();
                        }}
                      />
                    </div>
                  )}
                </div>
              )}
            </div>
          );
        })}
      </div>

      {/* Advance button for bottom */}
      <div className="flex justify-end">
        <button
          disabled={!allDone}
          onClick={onAdvance}
          className={`px-4 py-2 rounded-lg font-semibold ${
            allDone ? 'bg-emerald-600 text-white hover:bg-emerald-700' : 'bg-slate-700 text-slate-500'
          }`}
        >
          Advance →
        </button>
      </div>
    </div>
  );
}