'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import PipelineAdvanceButton from '../PipelineAdvanceButton';
import { SseLogPanel } from '../SseLogPanel';
import { extractJobIdFromSse } from '@/lib/client/sse-utils';

type ComponentStatus = 'done' | 'missing' | 'error' | 'running' | 'pending';

interface CompositionComponent {
  name: string;
  status: ComponentStatus;
  error?: string | null;
}

interface CompositionSection {
  id: string;
  label: string;
  components: CompositionComponent[];
  wrappers?: CompositionComponent[];
}

interface CompositionListResponse {
  sections: CompositionSection[];
  wrappers?: CompositionComponent[];
  artifactState?: {
    stale?: boolean;
    message?: string | null;
  };
}

interface StagingManifestEntry {
  filename: string;
  expected: boolean;
  present: boolean;
}

interface Stage8CompositionGenProps {
  onAdvance: () => void;
}

interface PreviewResponse {
  url?: string | null;
  path?: string | null;
  previewUrl?: string | null;
  specPath?: string | null;
  specContent?: string | null;
  error?: string | null;
  stale?: boolean;
}

const COLLAPSE_STORAGE_KEY = 'stage8-collapsed-sections';

/**
 * Renders a status badge with appropriate colors based on the component state.
 */
function StatusBadge({ status, error }: { status: ComponentStatus; error?: string | null }) {
  const styleMap: Record<ComponentStatus, string> = {
    done: 'bg-green-900/50 text-green-300 border-green-700',
    missing: 'bg-yellow-900/50 text-yellow-300 border-yellow-700',
    error: 'bg-red-900/50 text-red-300 border-red-700',
    running: 'bg-blue-900/50 text-blue-300 border-blue-700',
    pending: 'bg-slate-700 text-slate-200 border-slate-600',
  };

  const labelMap: Record<ComponentStatus, string> = {
    done: 'Done',
    missing: 'Missing',
    error: 'Error',
    running: 'Running',
    pending: 'Pending',
  };

  return (
    <span
      className={`inline-flex items-center rounded-full border px-2 py-0.5 text-xs font-medium ${styleMap[status]}`}
      title={status === 'error' && error ? error : undefined}
    >
      {labelMap[status]}
    </span>
  );
}

export default function Stage8CompositionGen({ onAdvance }: Stage8CompositionGenProps) {
  const [sections, setSections] = useState<CompositionSection[]>([]);
  const [stagingManifest, setStagingManifest] = useState<StagingManifestEntry[]>([]);
  const [loading, setLoading] = useState(true);
  const [listError, setListError] = useState<string | null>(null);
  const [manifestError, setManifestError] = useState<string | null>(null);
  const [artifactState, setArtifactState] = useState<{
    stale: boolean;
    message: string | null;
  }>({
    stale: false,
    message: null,
  });

  const [collapsed, setCollapsed] = useState<Record<string, boolean>>({});
  const [activeJobId, setActiveJobId] = useState<string | null>(null);
  const [logOpen, setLogOpen] = useState(false);

  const [previewUrl, setPreviewUrl] = useState<string | null>(null);
  const [previewName, setPreviewName] = useState<string | null>(null);
  const [previewSpecPath, setPreviewSpecPath] = useState<string | null>(null);
  const [previewSpecContent, setPreviewSpecContent] = useState<string | null>(null);
  const [previewError, setPreviewError] = useState<string | null>(null);
  const previewDialogRef = useRef<HTMLDialogElement | null>(null);

  const [actionBusy, setActionBusy] = useState<Record<string, boolean>>({});
  const [expandedErrorRows, setExpandedErrorRows] = useState<Set<string>>(new Set());

  const toggleErrorRow = (name: string, status: ComponentStatus) => {
    if (status !== 'error') return;
    setExpandedErrorRows((prev) => {
      const next = new Set(prev);
      next.has(name) ? next.delete(name) : next.add(name);
      return next;
    });
  };

  const totalComponents = useMemo(
    () => sections.reduce((sum, s) => sum + s.components.length, 0),
    [sections]
  );

  const sectionWrappers = useMemo(() => {
    const list: Array<{ sectionId: string; sectionLabel: string; wrapper: CompositionComponent }> = [];
    for (const section of sections) {
      for (const wrapper of section.wrappers ?? []) {
        list.push({
          sectionId: section.id,
          sectionLabel: section.label,
          wrapper,
        });
      }
    }
    return list;
  }, [sections]);

  const allWrapperNames = useMemo(
    () => sections.flatMap((s) => (s.wrappers ?? []).map((w) => w.name)),
    [sections]
  );

  const missingSectionComponents = useMemo(
    () => sections
      .map(s => ({
        sectionId: s.id,
        components: s.components.filter(c => c.status === 'missing').map(c => c.name),
      }))
      .filter(entry => entry.components.length > 0),
    [sections]
  );

  const missingComponentCount = useMemo(
    () => missingSectionComponents.reduce((sum, e) => sum + e.components.length, 0),
    [missingSectionComponents]
  );

  const loadCollapsed = () => {
    try {
      const raw = localStorage.getItem(COLLAPSE_STORAGE_KEY);
      if (raw) {
        const parsed = JSON.parse(raw) as Record<string, boolean>;
        setCollapsed(parsed);
      }
    } catch {
      // ignore
    }
  };

  const persistCollapsed = (next: Record<string, boolean>) => {
    try {
      localStorage.setItem(COLLAPSE_STORAGE_KEY, JSON.stringify(next));
    } catch {
      // ignore
    }
  };

  const refreshData = useCallback(async () => {
    setLoading(true);
    setListError(null);
    setManifestError(null);

    try {
      const res = await fetch('/api/pipeline/compositions/list');
      if (!res.ok) throw new Error(`Failed to load compositions (${res.status})`);
      const data = (await res.json()) as CompositionListResponse;
      setSections(data.sections ?? []);
      setArtifactState({
        stale: data.artifactState?.stale === true,
        message: data.artifactState?.message ?? null,
      });
    } catch (err) {
      setListError(err instanceof Error ? err.message : 'Failed to load compositions');
      setArtifactState({ stale: false, message: null });
    }

    try {
      const res = await fetch('/api/pipeline/veo/staging-manifest');
      if (!res.ok) throw new Error(`Failed to load staging manifest (${res.status})`);
      const data = (await res.json()) as StagingManifestEntry[];
      setStagingManifest(data ?? []);
    } catch (err) {
      setManifestError(err instanceof Error ? err.message : 'Failed to load manifest');
    }

    setLoading(false);
  }, []);

  useEffect(() => {
    loadCollapsed();
    refreshData();
  }, [refreshData]);

  // Periodically refresh component statuses while a job is active
  useEffect(() => {
    if (!activeJobId) return;
    const interval = setInterval(() => {
      refreshData();
    }, 5000);
    return () => clearInterval(interval);
  }, [activeJobId, refreshData]);

  const toggleSection = (id: string) => {
    setCollapsed((prev) => {
      const next = { ...prev, [id]: !prev[id] };
      persistCollapsed(next);
      return next;
    });
  };

  const runJob = async (
    url: string,
    payload?: Record<string, unknown>,
    busyKey?: string
  ) => {
    if (busyKey) {
      setActionBusy((prev) => ({ ...prev, [busyKey]: true }));
    }
    try {
      const res = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: payload ? JSON.stringify(payload) : undefined,
      });
      if (!res.ok) throw new Error(`Request failed (${res.status})`);
      const extractedJobId = await extractJobIdFromSse(res);
      if (extractedJobId) {
        setActiveJobId(extractedJobId);
        setLogOpen(true);
      }
    } catch (err) {
      console.error(err);
    } finally {
      if (busyKey) {
        setActionBusy((prev) => ({ ...prev, [busyKey]: false }));
      }
    }
  };

  const runAssetStaging = async (files: string[], busyKey?: string) => {
    if (busyKey) {
      setActionBusy((prev) => ({ ...prev, [busyKey]: true }));
    }
    setManifestError(null);

    try {
      const res = await fetch('/api/pipeline/asset-staging/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ files }),
      });

      let payload: { error?: string } | null = null;
      try {
        payload = (await res.json()) as { error?: string };
      } catch {
        payload = null;
      }

      if (!res.ok) {
        throw new Error(payload?.error ?? `Request failed (${res.status})`);
      }

      await refreshData();
    } catch (err) {
      const message = err instanceof Error ? err.message : 'Failed to stage assets';
      setManifestError(message);
      console.error(err);
    } finally {
      if (busyKey) {
        setActionBusy((prev) => ({ ...prev, [busyKey]: false }));
      }
    }
  };

  const openPreview = async (componentName: string, sectionId?: string) => {
    setPreviewName(componentName);
    setPreviewUrl(null);
    setPreviewSpecPath(null);
    setPreviewSpecContent(null);
    setPreviewError(null);
    try {
      const sectionParam = sectionId ? `&section=${encodeURIComponent(sectionId)}` : '';
      const res = await fetch(`/api/pipeline/compositions/preview?component=${encodeURIComponent(componentName)}${sectionParam}`);
      let previewPayload: PreviewResponse | null = null;
      if (res.headers.get('content-type')?.includes('application/json')) {
        previewPayload = (await res.json()) as PreviewResponse;
      }
      if (!res.ok) {
        throw new Error(previewPayload?.error ?? `Preview unavailable (${res.status})`);
      }
      let url: string | null = null;
      if (previewPayload) {
        url = previewPayload.url || previewPayload.path || previewPayload.previewUrl || null;
        setPreviewSpecPath(previewPayload.specPath ?? null);
        setPreviewSpecContent(previewPayload.specContent ?? null);
      } else {
        const text = (await res.text()).trim();
        url = (text.startsWith('http') || text.startsWith('/')) ? text : null;
      }
      if (!url) throw new Error('Preview unavailable');
      setPreviewUrl(url);
    } catch (err) {
      setPreviewUrl(null);
      setPreviewSpecPath(null);
      setPreviewSpecContent(null);
      setPreviewError(err instanceof Error ? err.message : 'Preview unavailable.');
    } finally {
      previewDialogRef.current?.showModal();
    }
  };

  const closePreview = () => {
    previewDialogRef.current?.close();
    setPreviewUrl(null);
    setPreviewName(null);
    setPreviewSpecPath(null);
    setPreviewSpecContent(null);
    setPreviewError(null);
  };

  const missingFiles = useMemo(
    () => stagingManifest.filter((entry) => entry.expected && !entry.present),
    [stagingManifest]
  );

  return (
    <div className="flex h-full flex-col gap-4">
      <div className="flex items-center justify-between">
        <div>
          <h2 className="text-lg font-semibold">Stage 8 · Composition Generation</h2>
          <p className="text-sm text-slate-500">
            Generate Remotion compositions, preview stills, and stage VEO assets.
          </p>
        </div>
        <PipelineAdvanceButton
          onClick={onAdvance}
          label="Continue →"
        />
      </div>

      <div className="grid gap-4 lg:grid-cols-2">
        {/* Left panel */}
        <div className="rounded-lg border border-slate-700 bg-slate-900 p-4 shadow-sm">
          <div className="mb-3 flex items-center justify-between">
            <h3 className="text-sm font-semibold text-slate-200">
              Components ({totalComponents})
            </h3>
            <div className="flex items-center gap-2">
              {missingComponentCount > 0 && (
                <button
                  className="rounded bg-amber-700 px-3 py-1.5 text-xs font-semibold text-white hover:bg-amber-600"
                  onClick={() => runJob('/api/pipeline/compositions/run', {
                    sectionComponents: missingSectionComponents,
                    wrappers: allWrapperNames,
                  }, 'generate-missing')}
                  disabled={actionBusy['generate-missing'] || actionBusy['generate-all']}
                >
                  {actionBusy['generate-missing'] ? 'Generating...' : `Generate Missing (${missingComponentCount})`}
                </button>
              )}
              <button
                className="rounded bg-slate-900 px-3 py-1.5 text-xs font-semibold text-white hover:bg-slate-800"
                onClick={() => runJob('/api/pipeline/compositions/run', {
                  sectionComponents: sections.map(s => ({
                    sectionId: s.id,
                    components: s.components.map(c => c.name),
                  })),
                  wrappers: allWrapperNames,
                }, 'generate-all')}
                disabled={actionBusy['generate-all'] || actionBusy['generate-missing']}
              >
                {actionBusy['generate-all'] ? 'Generating...' : 'Generate All Compositions'}
              </button>
            </div>
          </div>

          {loading && <p className="text-sm text-slate-500">Loading components…</p>}
          {listError && (
            <p className="rounded bg-red-900/50 px-3 py-2 text-sm text-red-300">{listError}</p>
          )}
          {artifactState.stale && (
            <p className="mb-3 rounded border border-amber-700 bg-amber-950/40 px-3 py-2 text-sm text-amber-200">
              {artifactState.message ?? 'Generated composition outputs are stale relative to the current generator/runtime. Regenerate compositions before previewing or rendering.'}{' '}
              Regenerate compositions to refresh Stage 8 artifacts.
            </p>
          )}

          {!loading &&
            sections.map((section) => {
              const isCollapsed = collapsed[section.id];
              return (
                <div key={section.id} className="mb-3 rounded border border-slate-700">
                  <button
                    className="flex w-full items-center justify-between px-3 py-2 text-left text-sm font-semibold text-slate-200 hover:bg-slate-700"
                    onClick={() => toggleSection(section.id)}
                  >
                    <span>{section.label}</span>
                    <span className="text-xs text-slate-500">
                      {isCollapsed ? 'Show' : 'Hide'}
                    </span>
                  </button>
                  {!isCollapsed && (
                    <div className="divide-y divide-slate-700">
                      {section.components.map((component) => (
                        <div key={component.name}>
                          <div
                            data-testid={`component-row-${component.name}`}
                            className={`flex items-center justify-between px-3 py-2 text-sm ${component.status === 'error' ? 'cursor-pointer hover:bg-slate-800' : ''}`}
                            onClick={() => toggleErrorRow(component.name, component.status)}
                          >
                            <div className="flex items-center gap-2">
                              <span className="font-medium text-slate-200">
                                {component.name}
                              </span>
                              <StatusBadge status={component.status} error={component.error} />
                            </div>
                            <div className="flex items-center gap-2">
                              <button
                                className="rounded border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                                onClick={(e) => { e.stopPropagation(); openPreview(component.name, section.id); }}
                              >
                                Preview
                              </button>
                              <button
                                className="rounded border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                                onClick={(e) => {
                                  e.stopPropagation();
                                  runJob(
                                    '/api/pipeline/compositions/run',
                                    { components: [component.name], sectionId: section.id },
                                    `regen-${component.name}`
                                  );
                                }}
                                disabled={actionBusy[`regen-${component.name}`]}
                              >
                                {actionBusy[`regen-${component.name}`] ? '...' : '↺'}
                              </button>
                            </div>
                          </div>
                          {component.status === 'error' && expandedErrorRows.has(component.name) && (
                            <div
                              data-testid={`error-log-drawer-${component.name}`}
                              className="border-t border-slate-700 bg-slate-800 px-3 py-2 font-mono text-xs text-red-300 whitespace-pre-wrap"
                            >
                              {component.error ?? 'No error details available.'}
                            </div>
                          )}
                        </div>
                      ))}
                      {section.components.length === 0 && (
                        <p className="px-3 py-2 text-xs text-slate-500">No components</p>
                      )}
                    </div>
                  )}
                </div>
              );
            })}

          <div className="mt-4">
            <h4 className="text-sm font-semibold text-slate-200">Section Wrappers</h4>
            <div className="mt-2 space-y-2">
              {sectionWrappers.length === 0 && (
                <p className="text-xs text-slate-500">No section wrappers available.</p>
              )}
              {sectionWrappers.map(({ wrapper, sectionId, sectionLabel }) => (
                <div
                  key={`${sectionId}-${wrapper.name}`}
                  className="flex items-center justify-between rounded border border-slate-700 px-3 py-2 text-sm"
                >
                  <div>
                    <p className="font-medium text-slate-200">{wrapper.name}</p>
                    <p className="text-xs text-slate-400">{sectionLabel}</p>
                  </div>
                  <div className="flex items-center gap-2">
                    <StatusBadge status={wrapper.status} error={wrapper.error} />
                    <button
                      className="rounded border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                      onClick={() => openPreview(wrapper.name, sectionId)}
                    >
                      Preview
                    </button>
                    <button
                      className="rounded border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                      onClick={() =>
                        runJob(
                          '/api/pipeline/compositions/run',
                          { wrappers: [wrapper.name] },
                          `regen-wrapper-${wrapper.name}`
                        )
                      }
                      disabled={actionBusy[`regen-wrapper-${wrapper.name}`]}
                    >
                      {actionBusy[`regen-wrapper-${wrapper.name}`] ? '...' : '↺'}
                    </button>
                  </div>
                </div>
              ))}
            </div>
          </div>
        </div>

        {/* Right panel */}
        <div className="rounded-lg border border-slate-700 bg-slate-900 p-4 shadow-sm">
          <div className="mb-3 flex items-center justify-between">
            <h3 className="text-sm font-semibold text-slate-200">Asset Staging Manifest</h3>
            <button
              className="rounded bg-slate-900 px-3 py-1.5 text-xs font-semibold text-white hover:bg-slate-800"
              onClick={() =>
                runAssetStaging(
                  missingFiles.map((f) => f.filename),
                  'stage-all'
                )
              }
              disabled={missingFiles.length === 0 || actionBusy['stage-all']}
            >
              {actionBusy['stage-all'] ? 'Staging...' : 'Stage All Missing'}
            </button>
          </div>

          {manifestError && (
            <p className="rounded bg-red-900/50 px-3 py-2 text-sm text-red-300">
              {manifestError}
            </p>
          )}

          <div className="overflow-x-auto">
            <table className="min-w-full text-sm">
              <thead className="border-b border-slate-700 text-left text-xs uppercase tracking-wide text-slate-400">
                <tr>
                  <th className="py-2 pr-2">Filename</th>
                  <th className="py-2 pr-2">Expected</th>
                  <th className="py-2 pr-2">Present</th>
                  <th className="py-2">Action</th>
                </tr>
              </thead>
              <tbody className="divide-y divide-slate-700">
                {stagingManifest.map((entry) => (
                  <tr key={entry.filename}>
                    <td className="py-2 pr-2 text-slate-200">{entry.filename}</td>
                    <td className="py-2 pr-2">
                      {entry.expected ? (
                        <span className="text-green-600">✓</span>
                      ) : (
                        <span className="text-slate-400">✗</span>
                      )}
                    </td>
                    <td className="py-2 pr-2">
                      {entry.present ? (
                        <span className="text-green-600">✓</span>
                      ) : (
                        <span className="text-red-500">✗</span>
                      )}
                    </td>
                    <td className="py-2">
                      {!entry.present && entry.expected && (
                        <button
                          className="rounded border border-slate-700 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                          onClick={() =>
                            runAssetStaging(
                              [entry.filename],
                              `stage-${entry.filename}`
                            )
                          }
                          disabled={actionBusy[`stage-${entry.filename}`]}
                        >
                          {actionBusy[`stage-${entry.filename}`] ? '...' : 'Stage Now'}
                        </button>
                      )}
                    </td>
                  </tr>
                ))}
                {stagingManifest.length === 0 && (
                  <tr>
                    <td colSpan={4} className="py-4 text-center text-xs text-slate-500">
                      No staging entries found.
                    </td>
                  </tr>
                )}
              </tbody>
            </table>
          </div>

          <div className="mt-4">
            <button
              className="flex w-full items-center justify-between rounded border border-slate-700 px-3 py-2 text-sm font-semibold text-slate-200 hover:bg-slate-700"
              onClick={() => setLogOpen((prev) => !prev)}
            >
              <span>Job Logs</span>
              <span className="text-xs text-slate-500">
                {logOpen ? 'Hide' : 'Show'}
              </span>
            </button>
            {logOpen && (
              <div className="mt-3 rounded border border-slate-700 bg-slate-800 p-3">
                <SseLogPanel
                  jobId={activeJobId}
                  onDone={() => {
                    setActiveJobId(null);
                    refreshData();
                  }}
                  onError={() => {
                    setActiveJobId(null);
                    refreshData();
                  }}
                />
              </div>
            )}
          </div>
        </div>
      </div>

      {/* Preview modal */}
      <dialog
        ref={previewDialogRef}
        className="fixed left-1/2 top-1/2 w-[min(92vw,1120px)] max-w-[1120px] -translate-x-1/2 -translate-y-1/2 rounded-lg border border-slate-700 bg-slate-900 p-0 text-white shadow-xl backdrop:bg-black/40"
      >
        <div className="flex items-center justify-between border-b border-slate-700 px-4 py-2">
          <div className="text-sm font-semibold text-slate-200">
            Preview {previewName ? `· ${previewName}` : ''}
          </div>
          <button
            className="rounded px-2 py-1 text-xs text-slate-400 hover:bg-slate-700"
            onClick={closePreview}
          >
            Close
          </button>
        </div>
        <div className="grid gap-4 p-4 lg:grid-cols-[minmax(0,1.2fr)_minmax(320px,0.8fr)]">
          <div className="rounded border border-slate-700 bg-slate-950/60 p-3">
            <div className="mb-3 text-sm font-semibold text-slate-200">Frame Preview</div>
            {previewUrl ? (
              <img src={previewUrl} alt="Preview still" className="max-h-[60vh] w-auto rounded border border-slate-700" />
            ) : (
              <div className="space-y-2">
                <p className="text-sm text-slate-500">Preview not available.</p>
                {previewError && previewError !== 'Preview not available.' ? (
                  <p className="text-xs text-slate-400">{previewError}</p>
                ) : null}
              </div>
            )}
          </div>
          <div className="rounded border border-slate-700 bg-slate-950/60 p-3">
            <div className="mb-1 text-sm font-semibold text-slate-200">Associated Spec</div>
            {previewSpecPath ? (
              <p className="mb-3 text-xs text-slate-400">{previewSpecPath}</p>
            ) : (
              <p className="mb-3 text-xs text-slate-500">No associated spec file found for this preview.</p>
            )}
            {previewSpecContent ? (
              <pre className="max-h-[60vh] overflow-auto whitespace-pre-wrap break-words rounded border border-slate-700 bg-slate-900 p-3 text-xs leading-6 text-slate-200">
                {previewSpecContent}
              </pre>
            ) : (
              <p className="text-sm text-slate-500">Spec content not available.</p>
            )}
          </div>
        </div>
      </dialog>
    </div>
  );
}
