'use client';

import React, { useCallback, useEffect, useState } from 'react';

interface FixPreview {
  annotationId: string;
  fixType: string;
  preview: string;
  diff: string | null;
  filesModified?: string[];
  confidence: number;
}

type Props = {
  sectionId: string;
  onClose: () => void;
  onApply: (annotationIds: string[]) => void;
};

export default function FixPreviewPanel({ sectionId, onClose, onApply }: Props) {
  const [previews, setPreviews] = useState<FixPreview[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [accepted, setAccepted] = useState<Set<string>>(() => new Set());
  const [expandedDiffs, setExpandedDiffs] = useState<Set<string>>(() => new Set());

  useEffect(() => {
    let cancelled = false;

    async function fetchPreviews() {
      setLoading(true);
      setError(null);
      try {
        const res = await fetch(`/api/sections/${sectionId}/preview-fixes`, {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
        });
        if (!res.ok) throw new Error(`Preview failed (${res.status})`);
        const data = await res.json();
        if (!cancelled) {
          setPreviews(data.previews || []);
          // Accept all by default
          setAccepted(new Set((data.previews || []).map((p: FixPreview) => p.annotationId)));
        }
      } catch (e) {
        if (!cancelled) setError(e instanceof Error ? e.message : 'Unknown error');
      } finally {
        if (!cancelled) setLoading(false);
      }
    }

    fetchPreviews();
    return () => { cancelled = true; };
  }, [sectionId]);

  const toggleAccepted = useCallback((id: string) => {
    setAccepted((prev) => {
      const next = new Set(prev);
      if (next.has(id)) next.delete(id);
      else next.add(id);
      return next;
    });
  }, []);

  const toggleDiff = useCallback((id: string) => {
    setExpandedDiffs((prev) => {
      const next = new Set(prev);
      if (next.has(id)) next.delete(id);
      else next.add(id);
      return next;
    });
  }, []);

  const acceptedCount = accepted.size;

  const handleApply = () => {
    onApply(Array.from(accepted));
  };

  const fixTypeColors: Record<string, string> = {
    remotion: 'bg-purple-500/20 text-purple-200',
    veo: 'bg-cyan-500/20 text-cyan-200',
    tts: 'bg-amber-500/20 text-amber-200',
  };

  return (
    <div className="rounded border border-white/10 bg-white/5 p-3">
      <div className="flex items-center justify-between mb-3">
        <div className="text-sm font-semibold text-white/90">Fix Preview</div>
        <button
          onClick={onClose}
          className="rounded bg-white/10 px-2 py-1 text-xs text-white/70 hover:bg-white/15"
        >
          Close
        </button>
      </div>

      {loading ? (
        <div className="flex items-center gap-2 py-4 text-xs text-white/60">
          <span className="inline-block h-4 w-4 animate-spin rounded-full border-2 border-white/30 border-t-white/80" />
          Generating previews...
        </div>
      ) : error ? (
        <div className="rounded bg-red-500/10 border border-red-500/20 p-2 text-xs text-red-200">
          {error}
        </div>
      ) : previews.length === 0 ? (
        <div className="py-4 text-xs text-white/60">No fixes to preview.</div>
      ) : (
        <>
          <div className="flex flex-col gap-2 max-h-96 overflow-y-auto">
            {previews.map((p) => (
              <div
                key={p.annotationId}
                className={`rounded border p-2 transition-colors ${
                  accepted.has(p.annotationId)
                    ? 'border-green-500/30 bg-green-500/5'
                    : 'border-white/10 bg-white/5'
                }`}
              >
                <div className="flex items-start gap-2">
                  <input
                    type="checkbox"
                    checked={accepted.has(p.annotationId)}
                    onChange={() => toggleAccepted(p.annotationId)}
                    className="mt-1 h-4 w-4 rounded border-white/30 bg-white/10"
                  />
                  <div className="flex-1 min-w-0">
                    <div className="flex items-center gap-2 mb-1">
                      <span className={`rounded px-2 py-0.5 text-[11px] font-medium ${fixTypeColors[p.fixType] || 'bg-white/10 text-white/80'}`}>
                        {p.fixType}
                      </span>
                      <span className="text-[11px] text-white/50">
                        {Math.round((p.confidence ?? 0) * 100)}% confidence
                      </span>
                    </div>
                    <div className="text-xs text-white/85">{p.preview}</div>
                    {(p.filesModified?.length ?? 0) > 0 ? (
                      <div className="mt-1 text-[11px] text-white/50">
                        Files: {p.filesModified?.join(', ')}
                      </div>
                    ) : null}
                    {p.diff ? (
                      <div className="mt-1">
                        <button
                          onClick={() => toggleDiff(p.annotationId)}
                          className="text-[11px] text-blue-300 hover:text-blue-200"
                        >
                          {expandedDiffs.has(p.annotationId) ? 'Hide diff' : 'Show diff'}
                        </button>
                        {expandedDiffs.has(p.annotationId) ? (
                          <pre className="mt-1 overflow-x-auto rounded bg-black/30 p-2 text-[11px] leading-relaxed text-white/80 whitespace-pre-wrap font-mono max-h-48 overflow-y-auto">
                            {p.diff}
                          </pre>
                        ) : null}
                      </div>
                    ) : null}
                  </div>
                </div>
              </div>
            ))}
          </div>

          <div className="mt-3 flex items-center justify-between">
            <div className="text-xs text-white/60">
              {acceptedCount} of {previews.length} fixes selected
            </div>
            <button
              onClick={handleApply}
              disabled={acceptedCount === 0}
              className="rounded bg-green-600 px-4 py-1.5 text-xs font-medium text-white hover:bg-green-500 disabled:cursor-not-allowed disabled:opacity-50"
            >
              Apply {acceptedCount} Fixes
            </button>
          </div>
        </>
      )}
    </div>
  );
}
