'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';

type AuditStatus = 'pending' | 'running' | 'done' | 'error';

type Verdict = 'PASS' | 'FAIL' | 'SKIP' | 'WARN';

type PlaybackWindow = {
  startSeconds: number;
  endSeconds: number;
  sampleSeconds: number;
  source: 'timestamp' | 'frame-range' | 'fallback';
};

interface SpecVerdict {
  specName: string;
  verdict: Verdict;
  summary: string;
  finding?: string;
  specPath?: string;
  playbackWindow?: PlaybackWindow;
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
  SKIP: 'bg-slate-700 text-slate-200',
  WARN: 'bg-amber-800 text-amber-200',
};

export default function Stage10Audit({ onAdvance, onCreateAnnotation }: Stage10AuditProps) {
  const [sections, setSections] = useState<SectionAudit[]>([]);
  const [expanded, setExpanded] = useState<Record<string, boolean>>({});
  const [specContent, setSpecContent] = useState<Record<string, string>>({});
  const [loadingSpec, setLoadingSpec] = useState<Record<string, boolean>>({});
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [auditDropdownOpen, setAuditDropdownOpen] = useState(false);
  const [activeVideoKey, setActiveVideoKey] = useState<string | null>(null);
  const auditDropdownRef = useRef<HTMLDivElement>(null);
  const mountedRef = useRef(true);

  useEffect(() => {
    mountedRef.current = true;
    return () => {
      mountedRef.current = false;
    };
  }, []);

  const refreshResults = useCallback(async (showLoading = false) => {
    try {
      if (showLoading && mountedRef.current) setLoading(true);
      if (mountedRef.current) setError(null);
      const res = await fetch('/api/pipeline/audit/results');
      if (!res.ok) throw new Error('Failed to load audit results.');
      const data: AuditResultsResponse = await res.json();
      if (mountedRef.current) setSections(data.sections || []);
    } catch (err: any) {
      if (mountedRef.current) {
        setError(err.message || 'Failed to load audit results.');
      }
    } finally {
      if (showLoading && mountedRef.current) setLoading(false);
    }
  }, []);

  useEffect(() => {
    void refreshResults(true);
  }, [refreshResults]);

  const applyAuditEvent = useCallback((data: Partial<SectionAudit> & { sectionId: string }) => {
    if (!mountedRef.current) return;
    setSections((prev) =>
      prev.map((section) =>
        section.sectionId === data.sectionId
          ? {
              ...section,
              passCount: data.passCount ?? section.passCount,
              failCount: data.failCount ?? section.failCount,
              status: data.status ?? section.status,
            }
          : section
      )
    );
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
    try {
      if (mountedRef.current) {
        setError(null);
        setSections((prev) =>
          prev.map((section) =>
            !sectionId || section.sectionId === sectionId
              ? { ...section, status: 'running' }
              : section
          )
        );
      }

      const res = await fetch('/api/pipeline/audit/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(sectionId ? { sections: [sectionId] } : {}),
      });

      if (!res.ok) {
        throw new Error('Failed to run audit.');
      }

      const reader = res.body?.getReader();
      if (!reader) {
        await refreshResults();
        return;
      }

      const decoder = new TextDecoder();
      let buffer = '';

      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        if (!mountedRef.current) break;

        buffer += decoder.decode(value, { stream: true });
        const parts = buffer.split('\n\n');
        buffer = parts.pop() ?? '';

        for (const part of parts) {
          const dataLine = part
            .split('\n')
            .find((line) => line.startsWith('data: '));
          if (!dataLine) continue;

          try {
            const data = JSON.parse(dataLine.slice(6));
            if (data?.type === 'audit-section' && typeof data.sectionId === 'string') {
              applyAuditEvent({
                sectionId: data.sectionId,
                passCount: data.passCount,
                failCount: data.failCount,
                status: data.status,
              });
            }

            if (data?.type === 'error') {
              if (mountedRef.current) {
                setError(data.message || 'Audit failed.');
              }
            }
          } catch {
            // Ignore malformed chunks and keep reading the stream.
          }
        }
      }

      await reader.cancel().catch(() => {});
      await refreshResults();
    } catch (err: any) {
      if (mountedRef.current) {
        setError(err.message || 'Failed to run audit.');
      }
      await refreshResults();
    }
  }, [applyAuditEvent, refreshResults]);

  const toggleExpanded = useCallback((sectionId: string) => {
    setExpanded((prev) => ({ ...prev, [sectionId]: !prev[sectionId] }));
  }, []);

  const toggleVideoPreview = useCallback((key: string) => {
    setActiveVideoKey((prev) => (prev === key ? null : key));
  }, []);

  const loadSpecContent = useCallback(
    async (key: string, specPath?: string) => {
      if (!specPath || specContent[key] || loadingSpec[key]) {
        return;
      }

      if (mountedRef.current) {
        setLoadingSpec((prev) => ({ ...prev, [key]: true }));
      }

      try {
        const res = await fetch(`/api/pipeline/specs/file?path=${encodeURIComponent(specPath)}`);
        if (!mountedRef.current) return;
        if (res.ok) {
          const data = await res.json();
          setSpecContent((prev) => ({ ...prev, [key]: data.content ?? '' }));
        } else {
          setSpecContent((prev) => ({ ...prev, [key]: 'Failed to load spec file.' }));
        }
      } catch {
        if (mountedRef.current) {
          setSpecContent((prev) => ({ ...prev, [key]: 'Failed to load spec file.' }));
        }
      } finally {
        if (mountedRef.current) {
          setLoadingSpec((prev) => ({ ...prev, [key]: false }));
        }
      }
    },
    [loadingSpec, specContent]
  );

  useEffect(() => {
    sections.forEach((section) => {
      if (!expanded[section.sectionId]) return;
      section.specs.forEach((spec) => {
        if (spec.verdict !== 'FAIL') return;
        const key = `${section.sectionId}:${spec.specName}`;
        void loadSpecContent(key, spec.specPath);
      });
    });
  }, [expanded, loadSpecContent, sections]);

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
                  {section.specs.length === 0 && (
                    <div className="p-3 text-xs text-white/50">No audit reports found yet.</div>
                  )}
                  {section.specs.map((spec) => {
                    const key = `${section.sectionId}:${spec.specName}`;
                    const frame = `/api/video/outputs/audit/${section.sectionId}/${spec.specName}_frame.png`;
                    const sectionVideo = `/api/video/outputs/sections/${section.sectionId}.mp4`;
                    const showInlineVideo = activeVideoKey === key;
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
                          <>
                            <div className="grid gap-3 px-2 pb-3 lg:grid-cols-2">
                              <div className="rounded border border-white/10 bg-black/20 p-2">
                                <div className="mb-2 text-[11px] font-semibold uppercase tracking-[0.18em] text-white/50">
                                  Frame Preview
                                </div>
                                <div className="overflow-hidden rounded border border-white/10">
                                  {showInlineVideo ? (
                                    <video
                                      src={sectionVideo}
                                      poster={frame}
                                      controls
                                      autoPlay
                                      preload="metadata"
                                      onLoadedMetadata={(event) => {
                                        if (!spec.playbackWindow) {
                                          return;
                                        }
                                        event.currentTarget.currentTime = spec.playbackWindow.startSeconds;
                                        void event.currentTarget.play().catch(() => {});
                                      }}
                                      onTimeUpdate={(event) => {
                                        if (!spec.playbackWindow) {
                                          return;
                                        }
                                        if (event.currentTarget.currentTime >= spec.playbackWindow.endSeconds) {
                                          event.currentTarget.currentTime = spec.playbackWindow.endSeconds;
                                          event.currentTarget.pause();
                                        }
                                      }}
                                      className="w-full bg-black/40"
                                    />
                                  ) : (
                                    <img
                                      src={frame}
                                      alt={`${spec.specName} audit frame`}
                                      className="w-full bg-black/40"
                                    />
                                  )}
                                </div>
                              </div>

                              <div className="rounded border border-white/10 bg-black/20 p-2">
                                <div className="mb-2 flex items-center justify-between gap-3 text-[11px] font-semibold uppercase tracking-[0.18em] text-white/50">
                                  <span>Spec Preview</span>
                                  {spec.specPath && (
                                    <span className="normal-case tracking-normal text-white/35">
                                      {spec.specPath}
                                    </span>
                                  )}
                                </div>
                                <div className="max-h-64 overflow-auto whitespace-pre-wrap rounded border border-white/10 bg-black/30 p-3 font-mono text-[11px] leading-relaxed text-white/80">
                                  {spec.specPath
                                    ? (loadingSpec[key] && !specContent[key]
                                        ? 'Loading spec...'
                                        : specContent[key] || 'Loading spec...')
                                    : 'No spec file linked.'}
                                </div>
                              </div>
                            </div>

                            <div className="flex gap-4 px-2 pb-2 text-xs text-white/60">
                              <button
                                className="text-blue-400 hover:underline"
                                onClick={() => toggleVideoPreview(key)}
                              >
                                Play Video
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
                          </>
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
    </div>
  );
}
