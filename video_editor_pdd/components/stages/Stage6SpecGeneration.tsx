'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import CodeMirror from '@uiw/react-codemirror';
import { markdown } from '@codemirror/lang-markdown';
import { EditorView } from '@codemirror/view';
import {
  extractNarrationSyncQuotes,
  findMatchingScriptSection,
  parseScriptSections,
  scriptLineMatchesNarration,
} from '@/lib/spec-script-context';
import {
  filterWordsForSpecTimingWindow,
  parseSpecTimingWindow,
} from '@/lib/spec-timing-context';
import { formatMarkdownDocument } from '@/lib/markdown-format';
import { MarkdownPreview } from '@/lib/markdown-preview';
import PipelineAdvanceButton from '../PipelineAdvanceButton';
import { readSseStartResult } from '../../lib/client/sse-utils';
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

type ScriptResponse = {
  content?: string;
};

type WordTimestamp = {
  word: string;
  start: number;
  end: number;
  segmentId?: string;
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

const scriptKindClasses: Record<string, string> = {
  visual: 'border-teal-700 bg-teal-900/40 text-teal-200',
  narrator: 'border-blue-700 bg-blue-900/40 text-blue-200',
  text: 'border-slate-700 bg-slate-800 text-slate-300',
};

const normalizeTimingText = (value: string): string =>
  value.toLowerCase().replace(/[^a-z0-9\s]/g, ' ').replace(/\s+/g, ' ').trim();

const formatTimingSeconds = (value: number): string => {
  if (!Number.isFinite(value)) return '0:00.00';
  const minutes = Math.floor(value / 60);
  const seconds = (value % 60).toFixed(2).padStart(5, '0');
  return `${minutes}:${seconds}`;
};

export const Stage6SpecGeneration: React.FC<Stage6SpecGenerationProps> = ({ onAdvance }) => {
  const [sections, setSections] = useState<SpecSection[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [scriptContent, setScriptContent] = useState('');
  const [scriptLoading, setScriptLoading] = useState(true);
  const [scriptError, setScriptError] = useState<string | null>(null);
  const [timingWords, setTimingWords] = useState<WordTimestamp[]>([]);
  const [timingLoading, setTimingLoading] = useState(false);
  const [timingError, setTimingError] = useState<string | null>(null);

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
  const [editorMode, setEditorMode] = useState<'edit' | 'preview'>('edit');
  const [editorLoading, setEditorLoading] = useState(false);
  const [saving, setSaving] = useState(false);

  const [latestJobId, setLatestJobId] = useState<string | null>(null);

  const saveTimerRef = useRef<NodeJS.Timeout | null>(null);
  const editorContainerRef = useRef<HTMLDivElement | null>(null);

  // Reusable spec list fetcher (called on mount and after regeneration)
  const fetchSpecList = useCallback(async () => {
    try {
      setLoading(true);
      const res = await fetch('/api/pipeline/specs/list');
      if (!res.ok) throw new Error(`Failed to fetch specs: ${res.status}`);
      const data = (await res.json()) as SpecListResponse;

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
      setLoading(false);
    }
  }, []);

  // Load spec list on mount
  useEffect(() => {
    fetchSpecList();
  }, [fetchSpecList]);

  useEffect(() => {
    let isMounted = true;

    const fetchScript = async () => {
      try {
        setScriptLoading(true);
        const res = await fetch('/api/project/script');
        if (!res.ok) throw new Error(`Failed to fetch script: ${res.status}`);
        const data = (await res.json()) as ScriptResponse;
        if (!isMounted) return;
        setScriptContent(data.content ?? '');
        setScriptError(null);
      } catch (err) {
        if (!isMounted) return;
        setScriptContent('');
        setScriptError((err as Error).message);
      } finally {
        if (isMounted) {
          setScriptLoading(false);
        }
      }
    };

    fetchScript();

    return () => {
      isMounted = false;
    };
  }, []);

  useEffect(() => {
    if (!selectedSectionId) {
      setTimingWords([]);
      setTimingError(null);
      setTimingLoading(false);
      return;
    }

    let isMounted = true;

    const fetchTiming = async () => {
      try {
        setTimingLoading(true);
        const res = await fetch(
          `/api/pipeline/audio-sync/timestamps?section=${encodeURIComponent(selectedSectionId)}`
        );

        if (!res.ok) {
          if (!isMounted) return;
          setTimingWords([]);
          setTimingError(res.status === 404 ? null : `Failed to fetch audio sync timing: ${res.status}`);
          return;
        }

        const data = await res.json();
        if (!isMounted) return;
        const words = Array.isArray(data?.words)
          ? data.words
          : Array.isArray(data)
            ? data
            : [];
        setTimingWords(words);
        setTimingError(null);
      } catch (err) {
        if (!isMounted) return;
        setTimingWords([]);
        setTimingError((err as Error).message);
      } finally {
        if (isMounted) {
          setTimingLoading(false);
        }
      }
    };

    fetchTiming();

    return () => {
      isMounted = false;
    };
  }, [selectedSectionId]);

  // Persist expanded state
  useEffect(() => {
    if (typeof window === 'undefined') return;
    localStorage.setItem(LOCAL_STORAGE_KEY, JSON.stringify(expanded));
  }, [expanded]);

  useEffect(() => {
    editorContainerRef.current?.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }, [selectedFile, selectedSectionId]);

  const handleToggleSection = useCallback((id: string) => {
    setExpanded((prev) => ({ ...prev, [id]: !prev[id] }));
  }, []);

  const runSpecs = useCallback(async (payload: object) => {
    try {
      const res = await fetch('/api/pipeline/specs/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload),
      });

      if (!res.ok) return;

      const { jobId, errorMessage } = await readSseStartResult(res);
      if (errorMessage) {
        setError(errorMessage);
      }
      if (jobId) {
        setError(null);
        setLatestJobId(jobId);
      }
    } catch {
      // Ignore network/parse errors — button should not get stuck
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
    setEditorMode('edit');
    setEditorLoading(true);
    setEditorValue('');
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

  const saveSpecFile = useCallback(async (contentOverride?: string) => {
    if (!selectedFile) return;
    setSaving(true);
    try {
      await fetch('/api/pipeline/specs/file', {
        method: 'PUT',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          path: selectedFile.path,
          content: contentOverride ?? editorValue,
        }),
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

  const handleFormatMarkdown = useCallback(async () => {
    const formatted = formatMarkdownDocument(editorValue);
    if (formatted === editorValue) return;
    if (saveTimerRef.current) {
      clearTimeout(saveTimerRef.current);
      saveTimerRef.current = null;
    }
    setEditorValue(formatted);
    await saveSpecFile(formatted);
  }, [editorValue, saveSpecFile]);

  const editorTitle = useMemo(() => {
    return selectedFile ? `Editing: ${selectedFile.path}` : 'Select a spec file to edit';
  }, [selectedFile]);

  const selectedSection = useMemo(() => {
    return sections.find((section) => section.id === selectedSectionId) ?? null;
  }, [sections, selectedSectionId]);

  const parsedScriptSections = useMemo(() => {
    return parseScriptSections(scriptContent);
  }, [scriptContent]);

  const selectedScriptSection = useMemo(() => {
    if (!selectedSection) return null;
    return findMatchingScriptSection(parsedScriptSections, selectedSection);
  }, [parsedScriptSections, selectedSection]);

  const narrationSyncQuotes = useMemo(() => {
    return extractNarrationSyncQuotes(editorValue);
  }, [editorValue]);

  const selectedSpecTimingWindow = useMemo(() => {
    return parseSpecTimingWindow(editorValue);
  }, [editorValue]);

  const selectedScriptHeading = useMemo(() => {
    if (selectedScriptSection) return selectedScriptSection.heading;
    if (selectedSection) return selectedSection.label;
    return 'No section selected';
  }, [selectedScriptSection, selectedSection]);

  const isHighlightedScriptLine = useCallback(
    (lineIndex: number) => {
      if (!selectedScriptSection) return false;
      const line = selectedScriptSection.lines[lineIndex];
      if (!line) return false;
      if (scriptLineMatchesNarration(line, narrationSyncQuotes)) return true;
      if (line.kind !== 'narrator') return false;
      const nextLine = selectedScriptSection.lines[lineIndex + 1];
      return nextLine ? scriptLineMatchesNarration(nextLine, narrationSyncQuotes) : false;
    },
    [narrationSyncQuotes, selectedScriptSection]
  );

  const highlightedTimingTokens = useMemo(() => {
    const tokens = narrationSyncQuotes
      .flatMap((quote) => normalizeTimingText(quote).split(' '))
      .filter((token) => token.length >= 3);
    return new Set(tokens);
  }, [narrationSyncQuotes]);

  const visibleTimingWords = useMemo(() => {
    return filterWordsForSpecTimingWindow(timingWords, selectedSpecTimingWindow);
  }, [selectedSpecTimingWindow, timingWords]);

  const isHighlightedTimingWord = useCallback(
    (word: WordTimestamp) => {
      const normalizedWord = normalizeTimingText(word.word);
      if (!normalizedWord) return false;
      return normalizedWord
        .split(' ')
        .some((token) => highlightedTimingTokens.has(token));
    },
    [highlightedTimingTokens]
  );

  const timingSummary = useMemo(() => {
    if (visibleTimingWords.length > 0) {
      const first = visibleTimingWords[0];
      const last = visibleTimingWords[visibleTimingWords.length - 1];
      return {
        wordCount: visibleTimingWords.length,
        start: first ? formatTimingSeconds(first.start) : '0:00.00',
        end: last ? formatTimingSeconds(last.end) : '0:00.00',
      };
    }

    if (!selectedSpecTimingWindow) return null;

    return {
      wordCount: 0,
      start: formatTimingSeconds(selectedSpecTimingWindow.startSeconds),
      end: formatTimingSeconds(selectedSpecTimingWindow.endSeconds),
    };
  }, [selectedSpecTimingWindow, visibleTimingWords]);

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
          <PipelineAdvanceButton
            onClick={onAdvance}
            label="Continue →"
          />
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
                      const isSelectedFile =
                        selectedSectionId === section.id && selectedFile?.path === file.path;
                      return (
                        <React.Fragment key={file.path}>
                          <tr className="border-t">
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

                          {isSelectedFile && (
                            <tr className="border-t border-slate-700 bg-slate-800/70">
                              <td colSpan={4} className="p-3">
                                <div
                                  ref={editorContainerRef}
                                  className="rounded border border-slate-700 bg-slate-800 p-3"
                                >
                                  <div className="mb-3 flex items-center justify-between gap-3">
                                    <div className="text-sm font-medium">{editorTitle}</div>
                                    <div className="flex items-center gap-3">
                                      <div className="inline-flex overflow-hidden rounded border border-slate-600">
                                        <button
                                          className={`px-2 py-1 text-xs ${
                                            editorMode === 'edit'
                                              ? 'bg-slate-700 text-slate-100'
                                              : 'text-slate-300 hover:bg-slate-700'
                                          }`}
                                          onClick={() => setEditorMode('edit')}
                                          disabled={!selectedFile}
                                        >
                                          Edit Markdown
                                        </button>
                                        <button
                                          className={`border-l border-slate-600 px-2 py-1 text-xs ${
                                            editorMode === 'preview'
                                              ? 'bg-slate-700 text-slate-100'
                                              : 'text-slate-300 hover:bg-slate-700'
                                          }`}
                                          onClick={() => setEditorMode('preview')}
                                          disabled={!selectedFile}
                                        >
                                          Preview Markdown
                                        </button>
                                      </div>
                                      <button
                                        className="rounded border border-slate-600 px-2 py-1 text-xs text-slate-300 hover:bg-slate-700 disabled:cursor-not-allowed disabled:opacity-50"
                                        onClick={handleFormatMarkdown}
                                        disabled={editorLoading || !selectedFile}
                                      >
                                        Format Markdown
                                      </button>
                                      {saving && <div className="text-xs text-slate-400">Saving…</div>}
                                    </div>
                                  </div>
                                  <div className="grid max-h-[500px] gap-3 xl:grid-cols-3 items-stretch">
                                    <div className="flex min-w-0 flex-col rounded border border-slate-700 bg-slate-900/60">
                                      <div className="border-b border-slate-700 px-3 py-2">
                                        <div className="text-sm font-medium text-slate-100">Script Context</div>
                                        <div className="text-xs text-slate-400">{selectedScriptHeading}</div>
                                      </div>
                                      <div className="flex min-h-0 flex-1 flex-col space-y-3 p-3">
                                        <div className="text-xs text-slate-400">
                                          Highlighted lines come from the spec&apos;s Narration Sync quote.
                                        </div>

                                        {narrationSyncQuotes.length > 0 ? (
                                          <div className="flex flex-wrap gap-2">
                                            {narrationSyncQuotes.map((quote) => (
                                              <span
                                                key={quote}
                                                className="rounded border border-amber-700 bg-amber-900/30 px-2 py-1 text-[11px] text-amber-200"
                                              >
                                                &quot;{quote}&quot;
                                              </span>
                                            ))}
                                          </div>
                                        ) : (
                                          <div className="text-xs text-slate-500">
                                            No Narration Sync quote found in this spec.
                                          </div>
                                        )}

                                        <div className="min-h-0 flex-1 space-y-1 overflow-y-auto">
                                          {scriptLoading && (
                                            <div className="text-sm text-slate-400">Loading script…</div>
                                          )}
                                          {!scriptLoading && scriptError && (
                                            <div className="text-sm text-red-400">
                                              Script unavailable: {scriptError}
                                            </div>
                                          )}
                                          {!scriptLoading && !scriptError && !selectedScriptSection && (
                                            <div className="text-sm text-slate-400">
                                              No matching script section found.
                                            </div>
                                          )}
                                          {!scriptLoading &&
                                            !scriptError &&
                                            selectedScriptSection?.lines.map((line, lineIndex) => {
                                              const isHighlighted = isHighlightedScriptLine(lineIndex);
                                              return (
                                                <div
                                                  key={`${line.lineNumber}-${line.rawText}`}
                                                  className={`grid grid-cols-[auto_auto_1fr] gap-3 rounded px-2 py-1 ${
                                                    isHighlighted
                                                      ? 'bg-amber-500/10 ring-1 ring-amber-500/40'
                                                      : 'bg-transparent'
                                                  }`}
                                                >
                                                  <span className="w-8 text-right font-mono text-[11px] text-slate-500">
                                                    {line.lineNumber}
                                                  </span>
                                                  <span
                                                    className={`inline-flex h-5 items-center rounded border px-1.5 text-[10px] uppercase tracking-wide ${
                                                      scriptKindClasses[line.kind]
                                                    }`}
                                                  >
                                                    {line.kind}
                                                  </span>
                                                  <span className="min-w-0 whitespace-pre-wrap font-mono text-xs text-slate-200">
                                                    {line.text}
                                                  </span>
                                                </div>
                                              );
                                            })}
                                        </div>
                                      </div>
                                    </div>

                                    <div className="flex min-w-0 flex-col rounded border border-slate-700 bg-slate-900/60">
                                      <div className="border-b border-slate-700 px-3 py-2">
                                        <div className="text-sm font-medium text-slate-100">Audio Sync Timing</div>
                                        <div className="text-xs text-slate-400">
                                          {selectedSection?.label ?? 'No section selected'}
                                        </div>
                                      </div>
                                      <div className="flex min-h-0 flex-1 flex-col space-y-3 p-3">
                                        <div className="text-xs text-slate-400">
                                          Stage 5 word timestamps for this section. Words matching the current Narration Sync quote are highlighted.
                                        </div>

                                        <div className="rounded border border-slate-700 bg-slate-800/50 px-2 py-1 text-[11px] text-slate-300">
                                          <span className="text-slate-500">Spec Window</span>{' '}
                                          {selectedSpecTimingWindow
                                            ? `${formatTimingSeconds(selectedSpecTimingWindow.startSeconds)} - ${formatTimingSeconds(selectedSpecTimingWindow.endSeconds)}`
                                            : 'Full section timeline'}
                                        </div>

                                        {timingSummary ? (
                                          <div className="grid grid-cols-3 gap-2 text-[11px] text-slate-300">
                                            <div className="rounded border border-slate-700 bg-slate-800/70 px-2 py-1">
                                              <div className="text-slate-500">Words</div>
                                              <div className="font-mono text-slate-100">{timingSummary.wordCount}</div>
                                            </div>
                                            <div className="rounded border border-slate-700 bg-slate-800/70 px-2 py-1">
                                              <div className="text-slate-500">Start</div>
                                              <div className="font-mono text-slate-100">{timingSummary.start}</div>
                                            </div>
                                            <div className="rounded border border-slate-700 bg-slate-800/70 px-2 py-1">
                                              <div className="text-slate-500">End</div>
                                              <div className="font-mono text-slate-100">{timingSummary.end}</div>
                                            </div>
                                          </div>
                                        ) : null}

                                        <div className="min-h-0 flex-1 space-y-1 overflow-y-auto">
                                          {timingLoading && (
                                            <div className="text-sm text-slate-400">Loading audio sync timing…</div>
                                          )}
                                          {!timingLoading && timingError && (
                                            <div className="text-sm text-red-400">
                                              Audio sync timing unavailable: {timingError}
                                            </div>
                                          )}
                                          {!timingLoading && !timingError && timingWords.length === 0 && (
                                            <div className="text-sm text-slate-400">
                                              No Audio Sync timing data found for this section.
                                            </div>
                                          )}
                                          {!timingLoading &&
                                            !timingError &&
                                            timingWords.length > 0 &&
                                            visibleTimingWords.length === 0 &&
                                            selectedSpecTimingWindow && (
                                              <div className="text-sm text-slate-400">
                                                No Audio Sync words fall inside this spec&apos;s timestamp window.
                                              </div>
                                            )}
                                          {!timingLoading &&
                                            !timingError &&
                                            visibleTimingWords.map((word, wordIndex) => {
                                              const isHighlighted = isHighlightedTimingWord(word);
                                              return (
                                                <div
                                                  key={`${word.segmentId ?? 'segment'}-${wordIndex}-${word.start}`}
                                                  className={`grid grid-cols-[auto_auto_1fr] gap-3 rounded px-2 py-1 ${
                                                    isHighlighted
                                                      ? 'bg-emerald-500/10 ring-1 ring-emerald-500/40'
                                                      : 'bg-transparent'
                                                  }`}
                                                >
                                                  <span className="w-20 text-right font-mono text-[11px] text-slate-500">
                                                    {formatTimingSeconds(word.start)}
                                                  </span>
                                                  <span className="w-20 text-right font-mono text-[11px] text-slate-600">
                                                    {formatTimingSeconds(word.end)}
                                                  </span>
                                                  <span className="min-w-0 whitespace-pre-wrap font-mono text-xs text-slate-200">
                                                    {word.word}
                                                  </span>
                                                </div>
                                              );
                                            })}
                                        </div>
                                      </div>
                                    </div>

                                    <div className="flex min-w-0 flex-col rounded border border-slate-700 bg-slate-900/60 p-3">
                                      <div className="mb-2 text-sm font-medium text-slate-100">Visual Spec</div>
                                      {editorMode === 'edit' ? (
                                        <CodeMirror
                                          value={editorValue}
                                          height="320px"
                                          extensions={[markdown(), EditorView.lineWrapping]}
                                          onChange={(value) => setEditorValue(value)}
                                          onBlur={handleEditorBlur}
                                          basicSetup={{ lineNumbers: true }}
                                          theme="dark"
                                        />
                                      ) : (
                                        <div className="min-h-0 flex-1 overflow-y-auto rounded border border-slate-700 bg-slate-950 p-4">
                                          <MarkdownPreview content={editorValue} />
                                        </div>
                                      )}
                                      {editorLoading && <div className="mt-2 text-xs text-slate-400">Loading file…</div>}
                                    </div>
                                  </div>
                                </div>
                              </td>
                            </tr>
                          )}
                        </React.Fragment>
                      );
                    })}
                  </tbody>
                </table>
              </div>
            )}
          </div>
        ))}

      <details className="mt-6 rounded border border-slate-700 bg-slate-900/60">
        <summary className="cursor-pointer px-4 py-3 text-sm font-medium text-slate-200">
          Spec Generation Logs
        </summary>
        <div className="border-t border-slate-700 p-4">
          <SseLogPanel jobId={latestJobId} onDone={fetchSpecList} logClassName="max-h-[50vh]" />
        </div>
      </details>
    </div>
  );
};

export default Stage6SpecGeneration;
