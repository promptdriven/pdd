'use client';

import React, { useEffect, useMemo, useState } from 'react';
import { SseLogPanel } from '../SseLogPanel';

type VeoClipStatus = 'done' | 'generating' | 'missing' | 'error';

interface VeoClip {
  id: string;
  sectionId: string;
  aspectRatio: string;
  status: VeoClipStatus;
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
  const [autoComposite, setAutoComposite] = useState(false);

  const [logs, setLogs] = useState<ClipLog[]>([]);
  const [jobId, setJobId] = useState<string | null>(null);

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
      if (!res.ok) throw new Error('Failed to start generation');
      const data = await res.json();
      if (data?.jobId) setJobId(data.jobId);
    } catch (err) {
      console.error(err);
    }
  };

  const handleRegenerateReference = async (refId: string) => {
    await fetch('/api/pipeline/veo/references/run', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ referenceId: refId }),
    });
    fetchClips();
  };

  if (loading) {
    return <div className="p-6 text-slate-500">Loading Veo clips…</div>;
  }

  if (error) {
    return <div className="p-6 text-red-500">Error: {error}</div>;
  }

  return (
    <div className="w-full h-full flex gap-6 p-6">
      {/* Left Column */}
      <div className="w-1/3 space-y-6">
        {/* Character References */}
        <div className="bg-white rounded-lg shadow p-4">
          <h3 className="font-semibold text-slate-800 mb-3">Character References</h3>
          {references.length === 0 ? (
            <p className="text-sm text-slate-500">No reference portraits found.</p>
          ) : (
            <div className="space-y-3">
              {references.map((ref) => (
                <div key={ref.id} className="flex items-center justify-between gap-3">
                  <div className="flex items-center gap-3">
                    <img
                      src={`/api/video/outputs/veo/references/${ref.id}.png`}
                      className="w-16 h-16 object-cover rounded"
                      alt={ref.label ?? ref.id}
                    />
                    <div className="text-sm text-slate-700">{ref.label ?? ref.id}</div>
                  </div>
                  <button
                    onClick={() => handleRegenerateReference(ref.id)}
                    className="text-xs text-blue-600 hover:text-blue-800"
                  >
                    ↺ Regenerate
                  </button>
                </div>
              ))}
            </div>
          )}
        </div>

        {/* Frame Chaining */}
        <div className="bg-white rounded-lg shadow p-4">
          <h3 className="font-semibold text-slate-800 mb-3">Frame Chaining</h3>
          <div className="space-y-3">
            {Object.entries(clipsBySection).map(([sectionId, clips]) => (
              <div key={sectionId}>
                <div className="font-medium text-slate-700 mb-1">{sectionId}</div>
                <div className="text-xs text-slate-600 space-y-1">
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
        <div className="flex items-center justify-between bg-white rounded-lg shadow p-4">
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
              value={selectedSection}
              onChange={(e) => setSelectedSection(e.target.value)}
              className="border rounded px-2 py-1 text-sm text-slate-800 bg-white"
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
          <div className="flex items-center gap-2 text-sm text-slate-700">
            <input
              type="checkbox"
              checked={autoComposite}
              onChange={(e) => setAutoComposite(e.target.checked)}
            />
            <span>Auto-composite split-screen</span>
          </div>
        </div>

        {/* Clip Table */}
        <div className="bg-white rounded-lg shadow overflow-hidden">
          <table className="w-full text-sm">
            <thead className="bg-slate-100 text-slate-600 text-xs uppercase">
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
                <tr key={clip.id} className="border-t">
                  <td className="px-4 py-2 font-medium text-slate-800">
                    {clip.id}{' '}
                    {clip.stale && <span className="text-amber-500 ml-1">⚠</span>}
                  </td>
                  <td className="px-4 py-2 text-slate-700">{clip.sectionId}</td>
                  <td className="px-4 py-2 text-slate-700">{clip.aspectRatio}</td>
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
          <SseLogPanel jobId={jobId} />
        </div>

        {/* Per-clip logs */}
        <div className="bg-white rounded-lg shadow p-4">
          <h3 className="font-semibold text-slate-800 mb-2" data-testid="clip-events-heading">Clip Events</h3>
          <div className="space-y-1 text-xs text-slate-600 max-h-40 overflow-y-auto font-mono">
            {logs.map((log, idx) => (
              <div key={idx}>
                [{new Date(log.ts).toLocaleTimeString()}] {log.clipId}: {log.message}
              </div>
            ))}
          </div>
        </div>

        {/* Advance */}
        <div className="flex justify-end">
          <button
            onClick={onAdvance}
            className="px-5 py-2 bg-emerald-600 text-white rounded-lg hover:bg-emerald-700"
          >
            Continue →
          </button>
        </div>
      </div>
    </div>
  );
}