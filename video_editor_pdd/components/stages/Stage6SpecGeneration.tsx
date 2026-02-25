'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import CodeMirror from '@uiw/react-codemirror';
import { markdown } from '@codemirror/lang-markdown';
import { SseLogPanel } from '../SseLogPanel';

interface Stage6SpecGenerationProps {
  onAdvance: () => void;
}

type SpecFile = {
  path: string;
  exists: boolean;
  // optional metadata from API
  firstLine?: string;
};

type SpecSection = {
  id: string;
  label: string;
  files: SpecFile[];
};

type SpecListResponse = {
  sections: SpecSection[];
};

type BadgeInfo = {
  label: string;
  colorClass: string;
};

const LOCAL_STORAGE_KEY = 'spec-sections-expanded';

const badgeFromFirstLine = (line?: string): BadgeInfo | null => {
  if (!line) return null;
  if (/\[Remotion\]/i.test(line)) {
    return { label: 'Remotion', colorClass: 'bg-blue-900/50 text-blue-300 border-blue-700' };
  }
  const veoMatch = line.match(/\[veo:.*?\]/i);
  if (veoMatch) {
    return { label: veoMatch[0].replace(/\[|\]/g, ''), colorClass: 'bg-purple-900/50 text-purple-300 border-purple-700' };
  }
  const titleMatch = line.match(/\[title:.*?\]/i);
  if (titleMatch) {
    return { label: titleMatch[0].replace(/\[|\]/g, ''), colorClass: 'bg-teal-900/50 text-teal-300 border-teal-700' };
  }
  const splitMatch = line.match(/\[split:.*?\]/i);
  if (splitMatch) {
    return { label: splitMatch[0].replace(/\[|\]/g, ''), colorClass: 'bg-orange-900/50 text-orange-300 border-orange-700' };
  }
  return null;
};

export const Stage6SpecGeneration: React.FC<Stage6SpecGenerationProps> = ({ onAdvance }) => {
  const [sections, setSections] = useState<SpecSection[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const [expanded, setExpanded] = useState<Record<string, boolean>>(() => {
    if (typeof window === 'undefined') return {};
    try {
      const stored = localStorage.getItem(LOCAL_STORAGE_KEY);
      return stored ? JSON.parse(stored) : {};
    } catch {
      return {};
    }
  });

  const [selectedFile, setSelectedFile] = useState<SpecFile | null>(null);
  const [selectedSectionId, setSelectedSectionId] = useState<string | null>(null);
  const [editorValue, setEditorValue] = useState('');
  const [editorLoading, setEditorLoading] = useState(false);
  const [saving, setSaving] = useState(false);

  const [latestJobId, setLatestJobId] = useState<string | null>(null);

  const saveTimerRef = useRef<NodeJS.Timeout | null>(null);

  // Load spec list
  useEffect(() => {
    let isMounted = true;
    const load = async () => {
      try {
        setLoading(true);
        const res = await fetch('/api/pipeline/specs/list');
        if (!res.ok) throw new Error(`Failed to fetch specs: ${res.status}`);
        const data = (await res.json()) as SpecListResponse;
        if (!isMounted) return;

        setSections(data.sections);

        // Initialize expanded defaults for new sections
        setExpanded((prev) => {
          const next = { ...prev };
          for (const section of data.sections) {
            if (next[section.id] === undefined) next[section.id] = true;
          }
          return next;
        });
      } catch (err) {
        setError((err as Error).message);
      } finally {
        if (isMounted) setLoading(false);
      }
    };
    load();
    return () => {
      isMounted = false;
    };
  }, []);

  // Persist expanded state
  useEffect(() => {
    if (typeof window === 'undefined') return;
    localStorage.setItem(LOCAL_STORAGE_KEY, JSON.stringify(expanded));
  }, [expanded]);

  const handleToggleSection = useCallback((id: string) => {
    setExpanded((prev) => ({ ...prev, [id]: !prev[id] }));
  }, []);

  const runSpecs = useCallback(async (payload: object) => {
    const res = await fetch('/api/pipeline/specs/run', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });

    if (res.ok) {
      const data = await res.json();
      if (data?.jobId) {
        setLatestJobId(data.jobId);
      }
    }
  }, []);

  const handleGenerateAll = useCallback(() => {
    runSpecs({});
  }, [runSpecs]);

  const handleRegenerateSection = useCallback(
    (sectionId: string) => {
      runSpecs({ sections: [sectionId] });
    },
    [runSpecs]
  );

  const handleRegenerateFile = useCallback(
    (filePath: string) => {
      runSpecs({ files: [filePath] });
    },
    [runSpecs]
  );

  const loadSpecFile = useCallback(async (file: SpecFile, sectionId: string) => {
    setSelectedFile(file);
    setSelectedSectionId(sectionId);
    setEditorLoading(true);
    try {
      const res = await fetch(`/api/pipeline/specs/file?path=${encodeURIComponent(file.path)}`);
      if (!res.ok) throw new Error(`Failed to load file: ${res.status}`);
      const data = await res.json();
      setEditorValue(data?.content ?? '');
    } catch (err) {
      setEditorValue(`Error loading file: ${(err as Error).message}`);
    } finally {
      setEditorLoading(false);
    }
  }, []);

  const saveSpecFile = useCallback(async () => {
    if (!selectedFile) return;
    setSaving(true);
    try {
      await fetch('/api/pipeline/specs/file', {
        method: 'PUT',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ path: selectedFile.path, content: editorValue }),
      });
    } finally {
      setSaving(false);
    }
  }, [selectedFile, editorValue]);

  const handleEditorBlur = useCallback(() => {
    if (saveTimerRef.current) clearTimeout(saveTimerRef.current);
    saveTimerRef.current = setTimeout(() => {
      saveSpecFile();
    }, 1000);
  }, [saveSpecFile]);

  const editorTitle = useMemo(() => {
    return selectedFile ? `Editing: ${selectedFile.path}` : 'Select a spec file to edit';
  }, [selectedFile]);

  return (
    <div className="w-full space-y-6">
      {/* Toolbar */}
      <div className="flex items-center justify-between gap-4 border-b pb-4">
        <h2 className="text-xl font-semibold">Stage 6 — Spec Generation</h2>
        <div className="flex items-center gap-2">
          <button
            className="rounded bg-indigo-600 px-4 py-2 text-white hover:bg-indigo-700"
            onClick={handleGenerateAll}
          >
            Generate All Specs
          </button>
          <button
            className="rounded border border-slate-600 px-3 py-2 text-slate-300 hover:bg-slate-700"
            onClick={onAdvance}
          >
            Continue →
          </button>
        </div>
      </div>

      {/* Content */}
      {loading && <div className="text-slate-500">Loading spec list…</div>}
      {error && <div className="text-red-500">Error: {error}</div>}

      {!loading && !error && sections.length === 0 && (
        <div className="text-slate-500">No spec sections found.</div>
      )}

      {!loading &&
        !error &&
        sections.map((section) => (
          <div key={section.id} className="rounded border border-slate-700 bg-slate-900">
            <div className="flex items-center justify-between px-4 py-3">
              <button
                className="flex items-center gap-2 text-left font-medium text-slate-200"
                onClick={() => handleToggleSection(section.id)}
              >
                <span>{expanded[section.id] ? '▾' : '▸'}</span>
                <span>{section.label}</span>
              </button>
              <button
                className="rounded border border-slate-600 px-2 py-1 text-xs text-slate-400 hover:bg-slate-700"
                onClick={() => handleRegenerateSection(section.id)}
                title="Regenerate section"
              >
                ↺ Regenerate
              </button>
            </div>

            {expanded[section.id] && (
              <div className="border-t px-4 py-4">
                <table className="w-full text-sm">
                  <thead>
                    <tr className="text-left text-slate-400">
                      <th className="py-2">Type</th>
                      <th className="py-2">Path</th>
                      <th className="py-2">Status</th>
                      <th className="py-2 text-right">Actions</th>
                    </tr>
                  </thead>
                  <tbody>
                    {section.files.map((file) => {
                      const badge = badgeFromFirstLine(file.firstLine);
                      return (
                        <tr key={file.path} className="border-t">
                          <td className="py-2">
                            {badge ? (
                              <span
                                className={`inline-flex items-center rounded border px-2 py-0.5 text-xs font-medium ${badge.colorClass}`}
                              >
                                [{badge.label}]
                              </span>
                            ) : (
                              <span className="text-xs text-slate-400">—</span>
                            )}
                          </td>
                          <td className="py-2 font-mono text-xs text-slate-300">{file.path}</td>
                          <td className="py-2">
                            {file.exists ? (
                              <span className="text-green-600">exists</span>
                            ) : (
                              <span className="text-red-500">missing</span>
                            )}
                          </td>
                          <td className="py-2 text-right">
                            <button
                              className="mr-2 rounded border border-slate-600 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                              onClick={() => loadSpecFile(file, section.id)}
                              title="Open in editor"
                            >
                              ✎
                            </button>
                            <button
                              className="rounded border border-slate-600 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700"
                              onClick={() => handleRegenerateFile(file.path)}
                              title="Regenerate file"
                            >
                              ↺
                            </button>
                          </td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>

                {/* Inline Editor — only shown in the section owning the selected file */}
                {selectedFile && selectedSectionId === section.id && (
                  <div className="mt-4 rounded border border-slate-700 bg-slate-800 p-3">
                    <div className="mb-2 flex items-center justify-between">
                      <div className="text-sm font-medium">{editorTitle}</div>
                      {saving && <div className="text-xs text-slate-400">Saving…</div>}
                    </div>
                    <CodeMirror
                      value={editorValue}
                      height="240px"
                      extensions={[markdown()]}
                      onChange={(value) => setEditorValue(value)}
                      onBlur={handleEditorBlur}
                      basicSetup={{ lineNumbers: true }}
                    />
                    {editorLoading && <div className="text-xs text-slate-400 mt-2">Loading file…</div>}
                  </div>
                )}
              </div>
            )}
          </div>
        ))}

      {/* SSE Log Drawer */}
      <details className="mt-6 rounded border border-slate-700 bg-slate-900">
        <summary className="cursor-pointer px-4 py-2 font-medium">Spec Generation Logs</summary>
        <div className="p-4">
          <SseLogPanel jobId={latestJobId} />
        </div>
      </details>
    </div>
  );
};

export default Stage6SpecGeneration;