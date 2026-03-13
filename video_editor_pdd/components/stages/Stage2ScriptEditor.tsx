'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import { EditorView } from '@codemirror/view';
import { EditorState } from '@codemirror/state';
import { markdown } from '@codemirror/lang-markdown';
import { keymap, type KeyBinding } from '@codemirror/view';
import { defaultKeymap } from '@codemirror/commands';
import PipelineAdvanceButton from '../PipelineAdvanceButton';
import SseLogPanel from '../SseLogPanel';
import { extractJobIdFromSse } from '@/lib/client/sse-utils';

type ScriptResponse = {
  content: string;
};

type PreviewBlock = {
  type: 'narrator' | 'visual' | 'header' | 'text';
  text: string;
};

interface Stage2ScriptEditorProps {
  onAdvance: () => void;
}

const SPLIT_KEY = 'script-editor-split-ratio';

const clampSplitRatio = (value: number) => Math.min(0.85, Math.max(0.15, value));

/**
 * Stage2ScriptEditor component provides a dual-pane interface for editing scripts.
 * It includes a CodeMirror editor on the left and a structured preview on the right.
 */
export default function Stage2ScriptEditor({ onAdvance }: Stage2ScriptEditorProps) {
  const editorContainerRef = useRef<HTMLDivElement | null>(null);
  const editorViewRef = useRef<EditorView | null>(null);

  const containerRef = useRef<HTMLDivElement | null>(null);
  const [splitRatio, setSplitRatio] = useState(0.5);

  const [content, setContent] = useState('');
  const contentRef = useRef('');
  const [previewBlocks, setPreviewBlocks] = useState<PreviewBlock[]>([]);
  const [loading, setLoading] = useState(true);
  const hasEditedRef = useRef(false);

  const [jobId, setJobId] = useState<string | null>(null);
  const [isGenerating, setIsGenerating] = useState(false);

  // Initialize split ratio from localStorage
  useEffect(() => {
    const stored = typeof window !== 'undefined' ? localStorage.getItem(SPLIT_KEY) : null;
    if (stored) {
      const parsed = parseFloat(stored);
      if (!Number.isNaN(parsed)) setSplitRatio(clampSplitRatio(parsed));
    }
  }, []);

  // Persist split ratio
  useEffect(() => {
    if (typeof window !== 'undefined') {
      localStorage.setItem(SPLIT_KEY, splitRatio.toString());
    }
  }, [splitRatio]);

  // Initialize CodeMirror (once on mount)
  useEffect(() => {
    if (!editorContainerRef.current || editorViewRef.current) return;

    const fullHeightTheme = EditorView.theme({
      '&': { height: '100%' },
      '.cm-scroller': { overflow: 'auto' },
    });

    const state = EditorState.create({
      doc: contentRef.current,
      extensions: [
        markdown(),
        keymap.of(defaultKeymap as unknown as KeyBinding[]),
        EditorView.lineWrapping,
        fullHeightTheme,
        EditorView.updateListener.of((update) => {
          if (update.docChanged) {
            const newContent = update.state.doc.toString();
            if (newContent !== contentRef.current) {
              hasEditedRef.current = true;
              contentRef.current = newContent;
              setContent(newContent);
            }
          }
        }),
      ],
    });

    editorViewRef.current = new EditorView({
      state,
      parent: editorContainerRef.current,
    });

    return () => {
      editorViewRef.current?.destroy();
      editorViewRef.current = null;
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // Load script content on mount
  useEffect(() => {
    let isMounted = true;

    const fetchScript = async () => {
      try {
        const res = await fetch('/api/project/script');
        const data: ScriptResponse = await res.json();
        if (!isMounted) return;

        setContent(data.content || '');
        contentRef.current = data.content || '';
      } catch (err) {
        console.error('Failed to load script:', err);
      } finally {
        if (isMounted) setLoading(false);
      }
    };

    fetchScript();

    return () => {
      isMounted = false;
    };
  }, []);

  // Sync loaded content into CodeMirror
  useEffect(() => {
    const view = editorViewRef.current;
    if (!view) return;
    const currentDoc = view.state.doc.toString();
    if (currentDoc !== content) {
      view.dispatch({
        changes: { from: 0, to: view.state.doc.length, insert: content },
      });
    }
  }, [content]);

  // Auto-save with debounce (1s) — only fires after user edits, not on initial load
  useEffect(() => {
    if (loading || !hasEditedRef.current) return;

    const id = setTimeout(async () => {
      try {
        await fetch('/api/project/script', {
          method: 'PUT',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ content }),
        });
      } catch (err) {
        console.error('Failed to save script:', err);
      }
    }, 1000);

    return () => clearTimeout(id);
  }, [content, loading]);

  // Structured preview parser
  const parsePreview = useCallback((text: string): PreviewBlock[] => {
    const lines = text.split(/\r?\n/);
    const blocks: PreviewBlock[] = [];

    for (const line of lines) {
      if (/^##\s+/.test(line)) {
        blocks.push({ type: 'header', text: line.replace(/^##\s+/, '') });
      } else if (/^\*{0,2}NARRATOR:\*{0,2}/.test(line)) {
        blocks.push({ type: 'narrator', text: line.replace(/^\*{0,2}NARRATOR:\*{0,2}\s*/, '' ) });
      } else if (/^\*{0,2}\[VISUAL:/.test(line)) {
        blocks.push({ type: 'visual', text: line.replace(/^\*{0,2}\[VISUAL:\s*/, '' ).replace(/\]\*{0,2}$/, '' ) });
      } else if (line.trim().length > 0) {
        blocks.push({ type: 'text', text: line });
      }
    }

    return blocks;
  }, []);

  // Debounced preview update (200ms)
  useEffect(() => {
    const id = setTimeout(() => {
      setPreviewBlocks(parsePreview(content));
    }, 200);

    return () => clearTimeout(id);
  }, [content, parsePreview]);

  const hasNarrator = useMemo(() => /NARRATOR:/m.test(content), [content]);

  // Handle TTS generation trigger
  const handleGenerateTts = async () => {
    if (!hasNarrator || isGenerating) return;

    setIsGenerating(true);
    try {
      const res = await fetch('/api/pipeline/tts-script/run', { method: 'POST' });
      if (!res.ok) throw new Error('Failed to start TTS generation');

      const jobId = await extractJobIdFromSse(res);
      if (jobId) {
        setJobId(jobId);
      }
    } catch (err) {
      console.error(err);
      setIsGenerating(false);
    }
  };

  const handleSseDone = () => {
    setIsGenerating(false);
    onAdvance();
  };

  const handleSseError = () => {
    setIsGenerating(false);
  };

  // Resizable split pane handlers
  const handleMouseDown = (e: React.MouseEvent) => {
    e.preventDefault();
    const startX = e.clientX;
    const container = containerRef.current;
    if (!container) return;

    const rect = container.getBoundingClientRect();
    const startRatio = splitRatio;

    const onMouseMove = (evt: MouseEvent) => {
      const delta = evt.clientX - startX;
      const newRatio = (startRatio * rect.width + delta) / rect.width;
      const clamped = clampSplitRatio(newRatio);
      setSplitRatio(clamped);
    };

    const onMouseUp = () => {
      window.removeEventListener('mousemove', onMouseMove);
      window.removeEventListener('mouseup', onMouseUp);
    };

    window.addEventListener('mousemove', onMouseMove);
    window.addEventListener('mouseup', onMouseUp);
  };

  return (
    <div className="w-full h-full flex flex-col">
      {/* Header */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-slate-700 bg-slate-900">
        <h2 className="text-lg font-semibold text-slate-100">Stage 2 — Script Editor</h2>
        <PipelineAdvanceButton
          onClick={handleGenerateTts}
          disabled={!hasNarrator || isGenerating}
          label={isGenerating ? 'Generating…' : 'Generate TTS Script & Continue →'}
          className="rounded-lg"
        />
      </div>

      {/* Main Split Pane */}
      <div ref={containerRef} className="flex-1 flex overflow-hidden bg-slate-900">
        {/* Left Pane - CodeMirror */}
        <div style={{ width: `${splitRatio * 100}%` }} className="h-full">
          <div className="h-full border-r border-slate-700">
            <div className="h-full" ref={editorContainerRef} />
          </div>
        </div>

        {/* Divider */}
        <div
          onMouseDown={handleMouseDown}
          className="w-2 cursor-col-resize bg-slate-700 hover:bg-slate-600 transition-colors"
        />

        {/* Right Pane - Structured Preview */}
        <div style={{ width: `${(1 - splitRatio) * 100}%` }} className="h-full overflow-y-auto">
          <div className="p-6 space-y-3">
            {previewBlocks.map((block, idx) => {
              if (block.type === 'header') {
                return (
                  <div key={`header-${idx}-${block.text.slice(0,20)}`} className="text-xs uppercase tracking-wider text-slate-500">
                    {block.text}
                  </div>
                );
              }

              if (block.type === 'narrator') {
                return (
                  <div key={`narrator-${idx}-${block.text.slice(0,20)}`} className="flex items-start gap-3 text-slate-300">
                    <span className="text-blue-500">■</span>
                    <span>{block.text}</span>
                  </div>
                );
              }

              if (block.type === 'visual') {
                return (
                  <div key={`visual-${idx}-${block.text.slice(0,20)}`} className="flex items-start gap-3 text-slate-300">
                    <span className="text-teal-500">▣</span>
                    <span>{block.text}</span>
                  </div>
                );
              }

              return (
                <div key={`text-${idx}-${block.text.slice(0,20)}`} className="text-slate-300">
                  {block.text}
                </div>
              );
            })}
          </div>
        </div>
      </div>

      {/* SSE Log Panel */}
      {jobId && (
        <div className="border-t border-slate-700 bg-slate-900">
          <SseLogPanel jobId={jobId} onDone={handleSseDone} onError={handleSseError} />
        </div>
      )}
    </div>
  );
}
