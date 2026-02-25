'use client';

import React, { useEffect, useMemo, useRef, useState } from 'react';
import type { Annotation, Job, JobStatus } from '../lib/types';
import { SseLogPanel } from './SseLogPanel';
import FixPreviewPanel from './FixPreviewPanel';

type Props = {
  annotations: Annotation[];
  sectionId: string;
  onBatchResolve: (jobId: string) => void;
};

const severityColors: Record<
  NonNullable<NonNullable<Annotation['analysis']>['severity']>,
  string
> = {
  critical: 'bg-red-500',
  major: 'bg-orange-500',
  minor: 'bg-yellow-500',
  pass: 'bg-green-500',
};

const fixTypeLabels: Record<
  NonNullable<NonNullable<Annotation['analysis']>['fixType']>,
  string
> = {
  remotion: 'Remotion Fix',
  veo: 'Veo Regen',
  tts: 'TTS Re-render',
  none: 'No Fix',
};

// Instruction helper (kept as-provided)
const formatTs = (s: number) => {
  const m = Math.floor(s / 60);
  const sec = (s % 60).toFixed(1);
  return `${m}:${sec.padStart(4, '0')}`;
};

function isTerminal(status: JobStatus | undefined | null) {
  return status === 'done' || status === 'error';
}

function useJob(jobId: string | null) {
  const [job, setJob] = useState<Job | null>(null);
  const [connected, setConnected] = useState(false);
  const eventSourceRef = useRef<EventSource | null>(null);

  useEffect(() => {
    let cancelled = false;
    setJob(null);
    setConnected(false);

    eventSourceRef.current?.close();
    eventSourceRef.current = null;

    if (!jobId) return;

    const fetchJob = async (id: string) => {
      const res = await fetch(`/api/jobs/${id}`, { cache: 'no-store' });
      if (!res.ok) return;
      const data = (await res.json()) as Job;
      if (!cancelled) setJob(data);
    };

    // Start with one fetch so UI isn't empty if SSE is slow.
    fetchJob(jobId).catch(() => {});

    // SSE: same stream used by SseLogPanel
    try {
      const es = new EventSource(`/api/jobs/${jobId}/stream`);
      eventSourceRef.current = es;

      es.onopen = () => {
        if (!cancelled) setConnected(true);
      };

      const refresh = () => fetchJob(jobId).catch(() => {});
      // Any streamed message implies progress; we refresh job snapshot.
      es.onmessage = () => refresh();
      es.addEventListener('done', () => refresh());
      es.addEventListener('error', () => refresh());
    } catch {
      // ignore; polling fallback below will handle.
    }

    // Polling fallback every 2s
    const interval = window.setInterval(() => {
      fetchJob(jobId).catch(() => {});
    }, 2000);

    return () => {
      cancelled = true;
      window.clearInterval(interval);
      eventSourceRef.current?.close();
      eventSourceRef.current = null;
    };
  }, [jobId]);

  return { job, connected };
}

function Spinner({ className = '' }: { className?: string }) {
  return (
    <span
      className={`inline-block h-4 w-4 animate-spin rounded-full border-2 border-white/30 border-t-white/80 ${className}`}
      aria-label="Loading"
    />
  );
}

/** Per-annotation card extracted as its own component so useJob can be called legally at the top level. */
function AnnotationCard({
  annotation: a,
  isLocallyResolved,
  defaultExpanded,
  onToggle,
  onRetryJob,
  onMarkResolved,
}: {
  annotation: Annotation;
  isLocallyResolved: boolean;
  defaultExpanded: boolean;
  onToggle: () => void;
  onRetryJob: (jobId: string) => void;
  onMarkResolved: (annotationId: string) => void;
}) {
  const [showDiff, setShowDiff] = useState(false);
  const [diffText, setDiffText] = useState<string | null>(null);
  const [diffLoading, setDiffLoading] = useState(false);
  const [reverting, setReverting] = useState(false);

  const isResolved = a.resolved || isLocallyResolved;
  const isExpanded = defaultExpanded;

  const analysis = a.analysis;
  const severity = analysis?.severity ?? null;
  const fixType = analysis?.fixType ?? null;

  const severityClass = severity ? severityColors[severity] : 'bg-white/10';
  const fixLabel = fixType ? fixTypeLabels[fixType] : 'Not analyzed';

  // Per-annotation job status (when resolveJobId set)
  const { job } = useJob(a.resolveJobId ?? null);

  const showInlineProgress = Boolean(a.resolveJobId) && !isTerminal(job?.status);
  const showFailed = Boolean(a.resolveJobId) && job?.status === 'error';

  const technicalAssessment = analysis?.technicalAssessment ?? '';
  const suggestedFixes = analysis?.suggestedFixes ?? [];

  const analysisSummary = analysis
    ? technicalAssessment.replace(/\s+/g, ' ').trim()
    : 'Awaiting analysis…';

  const handleViewDiff = async () => {
    if (showDiff) {
      setShowDiff(false);
      return;
    }
    if (!a.fixCommitSha) return;
    setDiffLoading(true);
    try {
      const res = await fetch(`/api/annotations/${a.id}/diff`);
      if (!res.ok) throw new Error('Failed to fetch diff');
      const data = await res.json();
      setDiffText(data.diff);
      setShowDiff(true);
    } catch (e) {
      console.error(e);
    } finally {
      setDiffLoading(false);
    }
  };

  const handleRevert = async () => {
    if (!a.fixCommitSha) return;
    if (!window.confirm('Revert this fix? This will create a new revert commit.')) return;
    setReverting(true);
    try {
      const res = await fetch(`/api/annotations/${a.id}/revert`, { method: 'POST' });
      if (!res.ok) throw new Error('Revert failed');
    } catch (e) {
      console.error(e);
    } finally {
      setReverting(false);
    }
  };

  return (
    <div
      className={`rounded border p-2 transition-colors ${
        isResolved
          ? 'border-green-500/30 bg-green-500/5'
          : 'border-white/10 bg-white/5 hover:bg-white/7'
      }`}
    >
      <button
        type="button"
        onClick={onToggle}
        className="w-full text-left"
        aria-expanded={isExpanded}
      >
        <div className="flex items-start gap-2">
          {a.compositeDataUrl ? (
            <img
              src={a.compositeDataUrl}
              className="w-20 h-11 object-cover rounded flex-shrink-0"
              alt={`Thumbnail at ${formatTs(a.timestamp)}`}
            />
          ) : (
            <div className="h-11 w-20 flex-shrink-0 rounded bg-white/5" />
          )}

          <div className="min-w-0 flex-1">
            <div className="flex items-center justify-between gap-2">
              <div className="text-xs font-mono text-white/70">
                {formatTs(a.timestamp)}
              </div>

              <div className="flex items-center gap-2">
                {showInlineProgress ? (
                  <span className="inline-flex items-center gap-2 rounded bg-white/10 px-2 py-0.5 text-[11px] text-white/80">
                    <Spinner className="h-3 w-3" />
                    {job?.status ?? 'running'}
                    {typeof job?.progress === 'number' ? ` ${job.progress}%` : ''}
                  </span>
                ) : null}

                {isResolved ? (
                  <span className="rounded bg-green-500/20 px-2 py-0.5 text-[11px] font-medium text-green-200">
                    ✓ Resolved
                  </span>
                ) : null}

                <span
                  className={`rounded px-2 py-0.5 text-[11px] font-medium text-black/90 ${severityClass}`}
                  title={severity ? `Severity: ${severity}` : 'No severity yet'}
                >
                  {severity ?? 'unknown'}
                </span>

                <span
                  className="rounded bg-white/10 px-2 py-0.5 text-[11px] font-medium text-white/80"
                  title={fixType ? `Fix type: ${fixType}` : 'No fix type yet'}
                >
                  {fixLabel}
                </span>
              </div>
            </div>

            <div className="mt-1">
              <div className="line-clamp-2 text-sm text-white/90">{a.text}</div>
              <div
                className="mt-1 line-clamp-1 text-xs text-white/60"
                title={analysisSummary}
              >
                {analysisSummary}
              </div>
            </div>
          </div>
        </div>
      </button>

      {isExpanded ? (
        <div className="mt-2 border-t border-white/10 pt-2">
          <div className="grid gap-2">
            <div>
              <div className="text-[11px] font-semibold text-white/70">
                Technical assessment
              </div>
              <div className="mt-1 whitespace-pre-wrap text-xs text-white/85">
                {analysis ? technicalAssessment : 'No analysis available.'}
              </div>
            </div>

            <div>
              <div className="text-[11px] font-semibold text-white/70">
                Suggested fixes
              </div>
              {analysis && suggestedFixes.length > 0 ? (
                <ul className="mt-1 list-disc space-y-1 pl-5 text-xs text-white/85">
                  {suggestedFixes.map((f, idx) => (
                    <li key={`${a.id}-fix-${idx}`}>{f}</li>
                  ))}
                </ul>
              ) : (
                <div className="mt-1 text-xs text-white/60">None.</div>
              )}
            </div>

            <div className="flex flex-wrap items-center justify-end gap-2">
              {a.fixCommitSha ? (
                <>
                  <button
                    onClick={handleViewDiff}
                    disabled={diffLoading}
                    className="rounded bg-blue-500/20 px-3 py-1.5 text-xs font-medium text-blue-200 hover:bg-blue-500/30 disabled:opacity-50"
                  >
                    {diffLoading ? 'Loading...' : showDiff ? 'Hide Diff' : 'View Diff'}
                  </button>
                  <button
                    onClick={handleRevert}
                    disabled={reverting}
                    className="rounded bg-red-500/20 px-3 py-1.5 text-xs font-medium text-red-200 hover:bg-red-500/30 disabled:opacity-50"
                  >
                    {reverting ? 'Reverting...' : 'Revert Fix'}
                  </button>
                </>
              ) : null}

              {showFailed && a.resolveJobId ? (
                <button
                  onClick={() => onRetryJob(a.resolveJobId!)}
                  className="rounded bg-white/10 px-3 py-1.5 text-xs font-medium text-white hover:bg-white/15"
                >
                  Retry
                </button>
              ) : null}

              {!isResolved ? (
                <button
                  onClick={() => onMarkResolved(a.id)}
                  className="rounded bg-white/10 px-3 py-1.5 text-xs font-medium text-white hover:bg-white/15"
                >
                  Mark Resolved
                </button>
              ) : null}
            </div>

            {showDiff && diffText ? (
              <div className="mt-2 rounded border border-white/10 bg-black/30 p-2">
                <div className="text-[11px] font-semibold text-white/70 mb-1">
                  Fix Diff ({a.fixCommitSha?.slice(0, 8)})
                </div>
                <pre className="overflow-x-auto text-[11px] leading-relaxed text-white/80 whitespace-pre-wrap font-mono max-h-64 overflow-y-auto">
                  {diffText}
                </pre>
              </div>
            ) : null}
          </div>
        </div>
      ) : null}
    </div>
  );
}

export default function AnnotationPanel({ annotations, sectionId, onBatchResolve }: Props) {
  const [expanded, setExpanded] = useState<Record<string, boolean>>({});
  const [batchJobId, setBatchJobId] = useState<string | null>(null);
  const [batchPosting, setBatchPosting] = useState(false);
  const [showPreview, setShowPreview] = useState(false);

  // Local-only resolve state (to support "Mark Resolved" without assuming an API exists).
  const [locallyResolvedIds, setLocallyResolvedIds] = useState<Set<string>>(() => new Set());

  const sorted = useMemo(() => {
    return [...annotations].sort((a, b) => a.timestamp - b.timestamp);
  }, [annotations]);

  const unresolvedWithAnalysisCount = useMemo(() => {
    return sorted.filter(
      (a) => !a.resolved && !locallyResolvedIds.has(a.id) && a.analysis !== null
    ).length;
  }, [sorted, locallyResolvedIds]);

  const batchInProgress = Boolean(batchJobId) && batchPosting;

  const handleToggle = (id: string) => {
    setExpanded((prev) => ({ ...prev, [id]: !prev[id] }));
  };

  const handleApplyBatch = () => {
    if (unresolvedWithAnalysisCount === 0) return;
    setShowPreview(true);
  };

  const handlePreviewApply = async (annotationIds: string[]) => {
    setShowPreview(false);
    setBatchPosting(true);
    try {
      const res = await fetch(`/api/sections/${sectionId}/resolve-batch`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ annotationIds }),
      });
      if (!res.ok) throw new Error(`Batch resolve failed (${res.status})`);
      const data = (await res.json()) as { jobId: string };
      setBatchJobId(data.jobId);
      onBatchResolve(data.jobId);
    } catch (e) {
      console.error(e);
    } finally {
      setBatchPosting(false);
    }
  };

  const handleRetryJob = async (jobId: string) => {
    try {
      const res = await fetch(`/api/jobs/${jobId}/retry`, { method: 'POST' });
      if (!res.ok) throw new Error(`Retry failed (${res.status})`);
    } catch (e) {
      console.error(e);
    }
  };

  const handleMarkResolved = (annotationId: string) => {
    setLocallyResolvedIds((prev) => {
      const next = new Set(prev);
      next.add(annotationId);
      return next;
    });
  };

  return (
    <div className="flex h-full flex-col gap-3">
      <div className="flex items-center justify-between gap-2">
        <div className="text-sm font-semibold text-white/90">Annotations</div>

        <button
          onClick={handleApplyBatch}
          disabled={unresolvedWithAnalysisCount === 0 || Boolean(batchJobId)}
          className="rounded bg-white/10 px-3 py-1.5 text-xs font-medium text-white hover:bg-white/15 disabled:cursor-not-allowed disabled:opacity-50"
          title={
            unresolvedWithAnalysisCount === 0
              ? 'No unresolved analyzed annotations'
              : batchJobId
                ? 'Batch resolve already in progress'
                : 'Apply fixes for unresolved analyzed annotations'
          }
        >
          {batchPosting ? (
            <span className="inline-flex items-center gap-2">
              <Spinner /> Applying…
            </span>
          ) : (
            `Apply ${unresolvedWithAnalysisCount} Fixes`
          )}
        </button>
      </div>

      {/* Batch SSE logs */}
      {batchJobId ? (
        <div className="rounded border border-white/10 bg-white/5 p-2">
          <div className="mb-2 flex items-center justify-between">
            <div className="text-xs font-medium text-white/80">Batch Resolve Job</div>
            <div className="text-[11px] text-white/60">jobId: {batchJobId}</div>
          </div>

          <SseLogPanel
            jobId={batchJobId}
            onDone={() => {
              // Parent is expected to refetch and pass updated annotations.
              // Keep the panel visible; user may want the logs.
            }}
            onError={() => {
              // Keep logs visible on error.
            }}
          />
        </div>
      ) : null}

      {showPreview ? (
        <FixPreviewPanel
          sectionId={sectionId}
          onClose={() => setShowPreview(false)}
          onApply={handlePreviewApply}
        />
      ) : null}

      <div className="min-h-0 flex-1 overflow-y-auto rounded border border-white/10 bg-black/10 p-2">
        <div className="flex flex-col gap-2">
          {sorted.length === 0 ? (
            <div className="p-3 text-xs text-white/60">No annotations yet.</div>
          ) : (
            sorted.map((a) => {
              const isLocallyResolved = locallyResolvedIds.has(a.id);
              const isResolved = a.resolved || isLocallyResolved;

              // Resolved annotations should be collapsed by default.
              const isExpanded = expanded[a.id] ?? false;

              return (
                <AnnotationCard
                  key={a.id}
                  annotation={a}
                  isLocallyResolved={isLocallyResolved}
                  defaultExpanded={isExpanded}
                  onToggle={() => handleToggle(a.id)}
                  onRetryJob={handleRetryJob}
                  onMarkResolved={handleMarkResolved}
                />
              );
            })
          )}
        </div>
      </div>
    </div>
  );
}
