'use client';

import React, { useEffect, useMemo, useState } from 'react';
import PipelineAdvanceButton from '../PipelineAdvanceButton';
import { SseLogPanel } from '../SseLogPanel';
import { extractJobIdFromSse } from '@/lib/client/sse-utils';

type VeoClipStatus = 'done' | 'generating' | 'missing' | 'error';

interface VeoClip {
  id: string;
  sectionId: string;
  aspectRatio: string;
  status: VeoClipStatus;
  specPath?: string | null;
  stale?: boolean;
  frameChainDeps?: string[];
}

interface ReferencePortrait {
  id: string;
  label?: string;
}

interface Stage7VeoGenerationProps {
  onAdvance: () => void;
}

interface ClipLog {
  clipId: string;
  message: string;
  ts: string;
}

const statusBadge = (status: VeoClipStatus) => {
  switch (status) {
    case 'done':
      return <span className="text-green-500 font-semibold">● done</span>;
    case 'generating':
      return <span className="text-amber-500 font-semibold animate-pulse">◌ generating</span>;
    case 'missing':
      return <span className="text-slate-400 font-semibold">○ missing</span>;
    case 'error':
      return <span className="text-red-500 font-semibold">✕ error</span>;
    default:
      return <span className="text-slate-400">unknown</span>;
  }
};

export default function Stage7VeoGeneration({ onAdvance }: Stage7VeoGenerationProps) {
  const [clips, setClips] = useState<VeoClip[]>([]);
  const [references, setReferences] = useState<ReferencePortrait[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const [selectedSection, setSelectedSection] = useState<string>('');
  const [selectedClipId, setSelectedClipId] = useState<string>('');
  const [selectedSpecContent, setSelectedSpecContent] = useState('');
  const [selectedSpecLoading, setSelectedSpecLoading] = useState(false);
  const [selectedSpecError, setSelectedSpecError] = useState<string | null>(null);
  const [autoComposite, setAutoComposite] = useState(false);

  const [logs, setLogs] = useState<ClipLog[]>([]);
  const [jobId, setJobId] = useState<string | null>(null);
  const [brokenRefs, setBrokenRefs] = useState<Set<string>>(new Set());
  const [brokenVideos, setBrokenVideos] = useState<Set<string>>(new Set());
  const [regeneratingRefId, setRegeneratingRefId] = useState<string | null>(null);

  const fetchClips = async () => {
    try {
      setLoading(true);
      setError(null);
      const res = await fetch('/api/pipeline/veo/clips');
      if (!res.ok) throw new Error('Failed to load clip list');
      const data = await res.json();

      // Support both array and object formats
      const fetchedClips: VeoClip[] = Array.isArray(data) ? data : data.clips ?? [];
      const fetchedRefs: ReferencePortrait[] = data.references ?? data.portraits ?? [];

      setClips(fetchedClips);
      setReferences(fetchedRefs);

      if (!selectedSection && fetchedClips.length > 0) {
        setSelectedSection(fetchedClips[0].sectionId);
      }
      if (!selectedClipId && fetchedClips.length > 0) {
        setSelectedClipId(fetchedClips[0].id);
      }
    } catch (err: any) {
      setError(err.message || 'Unknown error');
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    fetchClips();
  }, []);

  // SSE for per-clip progress events
  useEffect(() => {
    const es = new EventSource('/api/pipeline/veo/stream');
    es.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        if (data.clipId && data.message) {
          setLogs((prev) => [
            ...prev,
            { clipId: data.clipId, message: data.message, ts: new Date().toISOString() },
          ]);
        }
        if (data.clipId && data.status) {
          setClips((prev) =>
            prev.map((c) => (c.id === data.clipId ? { ...c, status: data.status } : c))
          );
        }
      } catch {
        // Ignore malformed SSE
      }
    };
    return () => {
      es.close();
    };
  }, []);

  const sections = useMemo(() => {
    return Array.from(new Set(clips.map((c) => c.sectionId)));
  }, [clips]);

  const clipsBySection = useMemo(() => {
    const map: Record<string, VeoClip[]> = {};
    for (const clip of clips) {
      if (!map[clip.sectionId]) map[clip.sectionId] = [];
      map[clip.sectionId].push(clip);
    }
    return map;
  }, [clips]);

  const selectedClip = useMemo(() => {
    return clips.find((clip) => clip.id === selectedClipId) ?? null;
  }, [clips, selectedClipId]);

  useEffect(() => {
    if (clips.length === 0) {
      setSelectedClipId('');
      return;
    }

    const hasSelectedClip = clips.some((clip) => clip.id === selectedClipId);
    if (!hasSelectedClip) {
      setSelectedClipId(clips[0].id);
    }
  }, [clips, selectedClipId]);

  useEffect(() => {
    let isMounted = true;

    const loadSelectedSpec = async () => {
      if (!selectedClip?.specPath) {
        setSelectedSpecContent('');
        setSelectedSpecError(null);
        setSelectedSpecLoading(false);
        return;
      }

      try {
        setSelectedSpecLoading(true);
        setSelectedSpecError(null);
        setSelectedSpecContent('');
        const res = await fetch(
          `/api/pipeline/specs/file?path=${encodeURIComponent(selectedClip.specPath)}`
        );
        if (!res.ok) {
          throw new Error(`Failed to load spec: ${res.status}`);
        }

        const data = await res.json();
        if (!isMounted) return;
        setSelectedSpecContent(data?.content ?? '');
      } catch (err) {
        if (!isMounted) return;
        setSelectedSpecError((err as Error).message);
      } finally {
        if (isMounted) {
          setSelectedSpecLoading(false);
        }
      }
    };

    loadSelectedSpec();

    return () => {
      isMounted = false;
    };
  }, [selectedClip]);

  const handleRunClips = async (clipIds: string[]) => {
    if (!clipIds.length) return;
    setClips((prev) =>
      prev.map((c) => (clipIds.includes(c.id) ? { ...c, status: 'generating' } : c))
    );
    try {
      const res = await fetch('/api/pipeline/veo/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ clips: clipIds, autoComposite }),
      });
      if (!res.ok) {
        // Revert optimistic status on error
        setClips((prev) =>
          prev.map((c) => (clipIds.includes(c.id) ? { ...c, status: 'error' } : c))
        );
        return;
      }
      const extractedJobId = await extractJobIdFromSse(res);
      if (extractedJobId) {
        setJobId(extractedJobId);
      } else {
        setClips((prev) =>
          prev.map((c) => (clipIds.includes(c.id) ? { ...c, status: 'error' } : c))
        );
      }
    } catch (err) {
      // Revert optimistic status on network/parse error
      setClips((prev) =>
        prev.map((c) => (clipIds.includes(c.id) ? { ...c, status: 'error' } : c))
      );
      console.error(err);
    }
  };

  const handleRegenerateReference = async (refId: string) => {
    setRegeneratingRefId(refId);
    try {
      const res = await fetch('/api/pipeline/veo/references/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ referenceId: refId }),
      });
      if (!res.ok) return;
      const extractedJobId = await extractJobIdFromSse(res);
      if (extractedJobId) setJobId(extractedJobId);
    } catch (err) {
      console.error(err);
    } finally {
      setRegeneratingRefId(null);
    }
  };

  if (loading) {
    return (
      <div className="p-6 space-y-4">
        <h2 className="text-xl font-semibold">Stage 7 — Veo Generation</h2>
        <div className="text-slate-500">Loading Veo clips…</div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="p-6 space-y-4">
        <h2 className="text-xl font-semibold">Stage 7 — Veo Generation</h2>
        <div className="text-red-500">Error: {error}</div>
      </div>
    );
  }

  return (
    <div className="w-full h-full flex flex-col gap-6 p-6">
      <h2 className="text-xl font-semibold">Stage 7 — Veo Generation</h2>
      <div className="flex gap-6 flex-1">
      {/* Left Column */}
      <div className="w-1/3 space-y-6">
        {/* Character References */}
        <div className="bg-slate-900 rounded-lg shadow border border-slate-700 p-4">
          <h3 className="font-semibold text-slate-200 mb-3">Character References</h3>
          {references.length === 0 ? (
            <p className="text-sm text-slate-500">No reference portraits found.</p>
          ) : (
            <div className="space-y-3">
              {references.map((ref) => (
                <div key={ref.id} className="flex items-center justify-between gap-3">
                  <div className="flex items-center gap-3">
                    {brokenRefs.has(ref.id) ? (
                      <div
                        data-testid="ref-portrait-fallback"
                        className="w-16 h-16 rounded bg-slate-700 flex items-center justify-center text-slate-500 text-xs"
                      >
                        No image
                      </div>
                    ) : (
                      <img
                        src={`/api/video/outputs/veo/references/${ref.id}.png`}
                        className="w-16 h-16 object-cover rounded"
                        alt={ref.label ?? ref.id}
                        onError={() =>
                          setBrokenRefs((prev) => new Set([...prev, ref.id]))
                        }
                      />
                    )}
                    <div className="text-sm text-slate-300">{ref.label ?? ref.id}</div>
                  </div>
                  <button
                    onClick={() => handleRegenerateReference(ref.id)}
                    disabled={regeneratingRefId === ref.id}
                    className="text-xs text-blue-600 hover:text-blue-800 disabled:opacity-50"
                  >
                    {regeneratingRefId === ref.id ? '⏳ Generating…' : '↺ Regenerate'}
                  </button>
                </div>
              ))}
            </div>
          )}
        </div>

        {/* Frame Chaining */}
        <div className="bg-slate-900 rounded-lg shadow border border-slate-700 p-4">
          <h3 className="font-semibold text-slate-200 mb-3">Frame Chaining</h3>
          <div className="space-y-3">
            {Object.entries(clipsBySection).map(([sectionId, clips]) => (
              <div key={sectionId}>
                <div className="font-medium text-slate-300 mb-1">{sectionId}</div>
                <div className="text-xs text-slate-400 space-y-1">
                  {clips.map((clip) => {
                    const deps = clip.frameChainDeps ?? [];
                    const chain =
                      deps.length > 0 ? `${deps.join(' → ')} → ${clip.id}` : clip.id;
                    return <div key={clip.id}>{chain}</div>;
                  })}
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>

      {/* Right Column */}
      <div className="flex-1 space-y-4">
        {/* Toolbar */}
        <div className="flex items-center justify-between bg-slate-900 rounded-lg shadow border border-slate-700 p-4">
          <div className="flex gap-2">
            <button
              onClick={() => handleRunClips(clips.map((c) => c.id))}
              className="px-3 py-1 text-sm bg-blue-600 text-white rounded hover:bg-blue-700"
            >
              Generate All
            </button>
            <button
              onClick={() =>
                handleRunClips(clips.filter((c) => c.status === 'missing').map((c) => c.id))
              }
              className="px-3 py-1 text-sm bg-slate-600 text-white rounded hover:bg-slate-700"
            >
              Generate Missing
            </button>
            <select
              aria-label="Section"
              data-testid="veo-section-select"
              value={selectedSection}
              onChange={(e) => setSelectedSection(e.target.value)}
              className="border border-slate-600 rounded px-2 py-1 text-sm text-slate-200 bg-slate-800"
            >
              {sections.map((section) => (
                <option key={section} value={section}>
                  {section}
                </option>
              ))}
            </select>
            <button
              onClick={() =>
                handleRunClips(clips.filter((c) => c.sectionId === selectedSection).map((c) => c.id))
              }
              className="px-3 py-1 text-sm bg-indigo-600 text-white rounded hover:bg-indigo-700"
            >
              Generate Section
            </button>
          </div>
          <div className="flex items-center gap-2 text-sm text-slate-300">
            <input
              type="checkbox"
              checked={autoComposite}
              onChange={(e) => setAutoComposite(e.target.checked)}
            />
            <span>Auto-composite split-screen</span>
          </div>
        </div>

        <div className="grid gap-4 xl:grid-cols-2" data-testid="veo-comparison-panel">
          <div className="bg-slate-900 rounded-lg shadow border border-slate-700 overflow-hidden">
            <div className="border-b border-slate-700 px-4 py-3">
              <div className="text-sm font-semibold text-slate-200">Veo Spec</div>
              <div className="text-xs text-slate-400">
                {selectedClip?.specPath ?? 'No canonical Veo markdown spec found for this clip'}
              </div>
            </div>
            <div className="p-4">
              {selectedSpecLoading && (
                <div className="text-sm text-slate-400">Loading canonical Veo spec…</div>
              )}
              {!selectedSpecLoading && selectedSpecError && (
                <div className="text-sm text-red-400">Error loading spec: {selectedSpecError}</div>
              )}
              {!selectedSpecLoading && !selectedSpecError && !selectedClip?.specPath && (
                <div className="text-sm text-slate-400">
                  No canonical Veo markdown spec found for this clip.
                </div>
              )}
              {!selectedSpecLoading && !selectedSpecError && selectedClip?.specPath && (
                <pre className="max-h-[360px] overflow-y-auto whitespace-pre-wrap rounded border border-slate-700 bg-slate-950/60 p-3 font-mono text-xs text-slate-200">
                  {selectedSpecContent}
                </pre>
              )}
            </div>
          </div>

          <div className="bg-slate-900 rounded-lg shadow border border-slate-700 overflow-hidden">
            <div className="border-b border-slate-700 px-4 py-3">
              <div className="text-sm font-semibold text-slate-200">Generated Video</div>
              <div className="text-xs text-slate-400">
                {selectedClip ? `${selectedClip.id} · ${selectedClip.aspectRatio}` : 'No clip selected'}
              </div>
            </div>
            <div className="p-4">
              {!selectedClip && (
                <div className="text-sm text-slate-400">Select a clip to compare its Veo spec and video.</div>
              )}
              {selectedClip && selectedClip.status !== 'done' && (
                <div className="rounded border border-slate-700 bg-slate-950/60 p-4 text-sm text-slate-400">
                  This clip is currently {selectedClip.status}. Generate it to compare the rendered video against the spec.
                </div>
              )}
              {selectedClip && selectedClip.status === 'done' && brokenVideos.has(selectedClip.id) && (
                <div className="rounded border border-red-700/60 bg-red-950/30 p-4 text-sm text-red-300">
                  The generated Veo video could not be loaded from disk.
                </div>
              )}
              {selectedClip && selectedClip.status === 'done' && !brokenVideos.has(selectedClip.id) && (
                <video
                  key={selectedClip.id}
                  controls
                  preload="metadata"
                  className="aspect-video w-full rounded border border-slate-700 bg-black"
                  src={`/api/video/outputs/veo/${selectedClip.id}.mp4`}
                  onError={() =>
                    setBrokenVideos((prev) => new Set([...prev, selectedClip.id]))
                  }
                />
              )}
            </div>
          </div>
        </div>

        {/* Clip Table */}
        <div className="bg-slate-900 rounded-lg shadow border border-slate-700 overflow-hidden">
          <table className="w-full text-sm">
            <thead className="bg-slate-800 text-slate-300 text-xs uppercase">
              <tr>
                <th className="text-left px-4 py-2">Clip</th>
                <th className="text-left px-4 py-2">Section</th>
                <th className="text-left px-4 py-2">Aspect</th>
                <th className="text-left px-4 py-2">Status</th>
                <th className="text-right px-4 py-2">Actions</th>
              </tr>
            </thead>
            <tbody>
              {clips.map((clip) => (
                <tr
                  key={clip.id}
                  className={`border-t cursor-pointer transition-colors hover:bg-slate-800/40 ${
                    selectedClipId === clip.id ? 'bg-slate-800/60' : ''
                  }`}
                  onClick={() => setSelectedClipId(clip.id)}
                >
                  <td className="px-4 py-2 font-medium text-slate-200">
                    {clip.id}{' '}
                    {clip.stale && <span className="text-amber-500 ml-1">⚠</span>}
                  </td>
                  <td className="px-4 py-2 text-slate-300">{clip.sectionId}</td>
                  <td className="px-4 py-2 text-slate-300">{clip.aspectRatio}</td>
                  <td className="px-4 py-2">{statusBadge(clip.status)}</td>
                  <td className="px-4 py-2 text-right">
                    <button
                      onClick={() => handleRunClips([clip.id])}
                      className="text-xs text-blue-600 hover:text-blue-800"
                    >
                      ↺ Regenerate
                    </button>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>

        {/* SSE Log Panel */}
        <div>
          <SseLogPanel jobId={jobId} onDone={() => { setJobId(null); fetchClips(); }} />
        </div>

        {/* Per-clip logs */}
        <div className="bg-slate-900 rounded-lg shadow border border-slate-700 p-4">
          <h3 className="font-semibold text-slate-200 mb-2" data-testid="clip-events-heading">Clip Events</h3>
          <div className="space-y-1 text-xs text-slate-400 max-h-40 overflow-y-auto font-mono">
            {logs.map((log, idx) => (
              <div key={idx}>
                [{new Date(log.ts).toLocaleTimeString()}] {log.clipId}: {log.message}
              </div>
            ))}
          </div>
        </div>

        {/* Advance */}
        <div className="flex justify-end">
          <PipelineAdvanceButton
            onClick={onAdvance}
            label="Continue →"
            className="rounded-lg px-5"
          />
        </div>
      </div>
      </div>
    </div>
  );
}
