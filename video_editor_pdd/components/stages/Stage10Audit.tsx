'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';

type AuditStatus = 'pending' | 'running' | 'done' | 'error';

type Verdict = 'PASS' | 'FAIL';

interface SpecVerdict {
  specName: string;
  verdict: Verdict;
  summary: string;
  finding?: string;
  specPath?: string;
}

interface SectionAudit {
  sectionId: string;
  sectionLabel: string;
  passCount: number;
  failCount: number;
  status: AuditStatus;
  specs: SpecVerdict[];
}

interface AuditResultsResponse {
  sections: SectionAudit[];
}

interface Stage10AuditProps {
  onAdvance: () => void;
  projectConfig?: any;
  /** Optional callback to prefill annotation form in parent (mapped from onCreateAnnotation) */
  onCreateAnnotation?: (data: {
    text: string;
    sectionId: string;
    compositeDataUrl: string;
    timestamp: number;
    drawingDataUrl: null;
    videoFile: string;
  }) => void;
}

const statusClasses: Record<AuditStatus, string> = {
  pending: 'bg-slate-700 text-slate-200',
  running: 'bg-amber-800 text-amber-200',
  done: 'bg-green-800 text-green-200',
  error: 'bg-red-800 text-red-200',
};

const verdictClasses: Record<Verdict, string> = {
  PASS: 'bg-green-800 text-green-200',
  FAIL: 'bg-red-800 text-red-200',
};

export default function Stage10Audit({ onAdvance, onCreateAnnotation }: Stage10AuditProps) {
  const [sections, setSections] = useState<SectionAudit[]>([]);
  const [expanded, setExpanded] = useState<Record<string, boolean>>({});
  const [specViewerOpen, setSpecViewerOpen] = useState<Record<string, boolean>>({});
  const [specContent, setSpecContent] = useState<Record<string, string>>({});
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [auditDropdownOpen, setAuditDropdownOpen] = useState(false);
  const auditDropdownRef = useRef<HTMLDivElement>(null);

  // Frame modal
  const dialogRef = useRef<HTMLDialogElement | null>(null);
  const [frameUrl, setFrameUrl] = useState<string | null>(null);

  // Load audit results on mount
  useEffect(() => {
    let mounted = true;
    const fetchResults = async () => {
      try {
        setLoading(true);
        setError(null);
        const res = await fetch('/api/pipeline/audit/results');
        if (!res.ok) throw new Error('Failed to load audit results.');
        const data: AuditResultsResponse = await res.json();
        if (mounted) setSections(data.sections || []);
      } catch (err: any) {
        if (mounted) setError(err.message || 'Failed to load audit results.');
      } finally {
        if (mounted) setLoading(false);
      }
    };
    fetchResults();
    return () => {
      mounted = false;
    };
  }, []);

  // SSE stream for per-agent progress
  useEffect(() => {
    const es = new EventSource('/api/pipeline/audit/stream');
    es.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        if (data.type === 'audit-section') {
          setSections((prev) =>
            prev.map((s) =>
              s.sectionId === data.sectionId
                ? {
                    ...s,
                    passCount: data.passCount ?? s.passCount,
                    failCount: data.failCount ?? s.failCount,
                    status: 'running',
                  }
                : s
            )
          );
        }
      } catch {
        // Ignore malformed events
      }
    };
    es.onerror = () => {
      es.close();
    };
    return () => es.close();
  }, []);

  useEffect(() => {
    if (!auditDropdownOpen) return;
    const handleClickOutside = (e: MouseEvent) => {
      if (auditDropdownRef.current && !auditDropdownRef.current.contains(e.target as Node)) {
        setAuditDropdownOpen(false);
      }
    };
    document.addEventListener('mousedown', handleClickOutside);
    return () => document.removeEventListener('mousedown', handleClickOutside);
  }, [auditDropdownOpen]);

  const handleAuditRun = useCallback(async (sectionId?: string) => {
    await fetch('/api/pipeline/audit/run', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(sectionId ? { sectionId } : {}),
    });
  }, []);

  const toggleExpanded = useCallback((sectionId: string) => {
    setExpanded((prev) => ({ ...prev, [sectionId]: !prev[sectionId] }));
  }, []);

  const openFrameModal = useCallback((url: string) => {
    setFrameUrl(url);
    dialogRef.current?.showModal();
  }, []);

  const closeFrameModal = useCallback(() => {
    dialogRef.current?.close();
    setFrameUrl(null);
  }, []);

  const toggleSpecViewer = useCallback(
    async (sectionId: string, specName: string, specPath?: string) => {
      const key = `${sectionId}:${specName}`;
      setSpecViewerOpen((prev) => ({ ...prev, [key]: !prev[key] }));
      if (!specContent[key] && specPath) {
        const res = await fetch(`/api/pipeline/specs/file?path=${encodeURIComponent(specPath)}`);
        if (res.ok) {
          const data = await res.json();
          setSpecContent((prev) => ({ ...prev, [key]: data.content ?? '' }));
        } else {
          setSpecContent((prev) => ({ ...prev, [key]: 'Failed to load spec file.' }));
        }
      }
    },
    [specContent]
  );

  const handleCreateAnnotation = useCallback(
    (sectionId: string, finding: string, frameUrl: string) => {
      onCreateAnnotation?.({
        text: finding,
        sectionId,
        compositeDataUrl: frameUrl,
        timestamp: 0,
        drawingDataUrl: null,
        videoFile: '',
      });
    },
    [onCreateAnnotation]
  );

  const sectionOptions = useMemo(
    () => sections.map((s) => ({ id: s.sectionId, label: s.sectionLabel })),
    [sections]
  );

  return (
    <div className="space-y-6">
      <header className="flex items-center justify-between">
        <h2 className="text-xl font-semibold">Audit Results</h2>

        <div className="flex items-center gap-2">
          <button
            onClick={() => handleAuditRun()}
            className="px-3 py-1.5 rounded bg-slate-900 text-white text-sm"
          >
            Audit All Sections
          </button>

          <div className="relative" ref={auditDropdownRef}>
            <button
              onClick={() => setAuditDropdownOpen((prev) => !prev)}
              className="cursor-pointer px-3 py-1.5 rounded bg-white/10 text-white text-sm"
            >
              Audit Section ▾
            </button>
            {auditDropdownOpen && (
              <div className="absolute right-0 mt-2 bg-gray-800 border border-white/10 rounded shadow-md z-10 w-48">
                {sectionOptions.map((opt) => (
                  <button
                    key={opt.id}
                    onClick={() => {
                      handleAuditRun(opt.id);
                      setAuditDropdownOpen(false);
                    }}
                    className="w-full text-left px-3 py-2 hover:bg-white/10 text-sm text-white"
                  >
                    {opt.label}
                  </button>
                ))}
              </div>
            )}
          </div>
        </div>
      </header>

      {loading && (
        <div className="animate-pulse space-y-2">
          <div className="h-8 bg-white/10 rounded" />
          <div className="h-8 bg-white/10 rounded" />
          <div className="h-8 bg-white/10 rounded" />
        </div>
      )}

      {error && (
        <div className="p-4 bg-red-900/30 border border-red-500/30 rounded text-red-300">
          {error}
        </div>
      )}

      {!loading && !error && sections.length === 0 && (
        <div className="text-white/60">No audit results available.</div>
      )}

      {!loading && !error && sections.length > 0 && (
        <div className="border border-white/10 rounded overflow-hidden">
          <div className="grid grid-cols-6 gap-2 p-3 bg-white/5 text-sm font-medium text-white">
            <div>Section</div>
            <div>Pass</div>
            <div>Fail</div>
            <div>Status</div>
            <div className="col-span-2 text-right">Actions</div>
          </div>

          {sections.map((section) => (
            <div key={section.sectionId} className="border-t border-white/10">
              <div className="grid grid-cols-6 gap-2 p-3 items-center text-sm text-white">
                <div>{section.sectionLabel}</div>
                <div>{section.passCount}</div>
                <div>{section.failCount}</div>
                <div>
                  <span
                    className={`px-2 py-0.5 rounded text-xs ${statusClasses[section.status]}`}
                  >
                    {section.status}
                  </span>
                </div>
                <div className="col-span-2 text-right space-x-2">
                  <button
                    className="text-blue-400 hover:underline"
                    onClick={() => toggleExpanded(section.sectionId)}
                  >
                    View Report
                  </button>
                  <button
                    className="text-white/60 hover:underline"
                    onClick={() => handleAuditRun(section.sectionId)}
                  >
                    ↺ Audit
                  </button>
                </div>
              </div>

              {expanded[section.sectionId] && (
                <div className="bg-white/5 border-t border-white/10">
                  <div className="grid grid-cols-12 gap-2 p-2 text-xs font-semibold text-white/60">
                    <div className="col-span-2">Verdict</div>
                    <div className="col-span-3">Spec</div>
                    <div className="col-span-7">Summary</div>
                  </div>
                  {section.specs.map((spec) => {
                    const key = `${section.sectionId}:${spec.specName}`;
                    const frame = `/api/video/outputs/audit/${section.sectionId}/${spec.specName}_frame.png`;
                    return (
                      <div key={key} className="border-t border-white/10">
                        <div className="grid grid-cols-12 gap-2 p-2 items-center text-sm">
                          <div className="col-span-2">
                            <span
                              className={`px-2 py-0.5 rounded text-xs ${verdictClasses[spec.verdict]}`}
                            >
                              {spec.verdict}
                            </span>
                          </div>
                          <div className="col-span-3 font-mono text-xs text-white/80">{spec.specName}</div>
                          <div className="col-span-7 text-white/70">{spec.summary}</div>
                        </div>

                        {spec.verdict === 'FAIL' && (
                          <div className="flex gap-4 px-2 pb-2 text-xs text-white/60">
                            <button
                              className="text-blue-400 hover:underline"
                              onClick={() => openFrameModal(frame)}
                            >
                              View Frame
                            </button>
                            <button
                              className="text-blue-400 hover:underline"
                              onClick={() =>
                                toggleSpecViewer(section.sectionId, spec.specName, spec.specPath)
                              }
                            >
                              View Spec
                            </button>
                            <button
                              className="text-blue-400 hover:underline"
                              onClick={() =>
                                handleCreateAnnotation(
                                  section.sectionId,
                                  spec.finding || spec.summary,
                                  frame
                                )
                              }
                            >
                              Create Annotation →
                            </button>
                          </div>
                        )}

                        {specViewerOpen[key] && (
                          <pre className="text-xs overflow-auto max-h-64 bg-black/30 border-t border-white/10 p-2 text-white/80">
                            {specContent[key] || 'Loading spec...'}
                          </pre>
                        )}
                      </div>
                    );
                  })}
                </div>
              )}
            </div>
          ))}
        </div>
      )}

      <dialog ref={dialogRef} className="rounded-lg p-0 max-w-3xl w-full bg-gray-900 text-white">
        <div className="p-4 border-b border-white/10 flex justify-between items-center">
          <span className="font-semibold text-white">Audit Frame</span>
          <button onClick={closeFrameModal} className="text-white/50 hover:text-white/80">
            ✕
          </button>
        </div>
        {frameUrl && (
          <div className="p-4">
            <img src={frameUrl} alt="Audit frame" className="max-w-full rounded" />
          </div>
        )}
      </dialog>
    </div>
  );
}