'use client';

import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import { diffLines } from 'diff';
import CodeMirror from '@uiw/react-codemirror';
import { markdown } from '@codemirror/lang-markdown';
import SseLogPanel from '../SseLogPanel';

interface Stage3TtsScriptGenProps {
  onAdvance: () => void;
}

type DiffLineType = 'added' | 'removed' | 'unchanged' | 'empty';

interface DiffLine {
  type: DiffLineType;
  text: string;
}

const LAST_RUN_KEY = 'tts-script-last-run';

export default function Stage3TtsScriptGen({ onAdvance }: Stage3TtsScriptGenProps) {
  const [mainScript, setMainScript] = useState<string>('');
  const [ttsScript, setTtsScript] = useState<string>('');
  const [ttsExists, setTtsExists] = useState<boolean>(false);
  const [jobId, setJobId] = useState<string | null>(null);
  const [lastRunTime, setLastRunTime] = useState<string | null>(null);
  const [loading, setLoading] = useState<boolean>(true);
  const [saving, setSaving] = useState<boolean>(false);
  const [isGenerating, setIsGenerating] = useState<boolean>(false);
  const [generateError, setGenerateError] = useState<string | null>(null);

  const debounceRef = useRef<NodeJS.Timeout | null>(null);
  const savingRef = useRef<boolean>(false);
  const generatingRef = useRef<boolean>(false);
  const pendingSaveRef = useRef<string | null>(null);

  const fetchScript = useCallback(async (file: 'main' | 'tts') => {
    try {
      const res = await fetch(`/api/project/script?file=${file}`);
      if (!res.ok) return null;
      const data = await res.json();
      return data?.content ?? null;
    } catch {
      return null;
    }
  }, []);

  const loadScripts = useCallback(async () => {
    setLoading(true);
    const [main, tts] = await Promise.all([fetchScript('main'), fetchScript('tts')]);
    setMainScript(main ?? '');
    setTtsScript(tts ?? '');
    setTtsExists(Boolean(tts));
    setLoading(false);
  }, [fetchScript]);

  useEffect(() => {
    loadScripts();
  }, [loadScripts]);

  useEffect(() => {
    const stored = localStorage.getItem(LAST_RUN_KEY);
    if (stored) setLastRunTime(stored);
  }, []);

  const saveTtsScript = useCallback(
    async (content: string) => {
      if (savingRef.current) {
        pendingSaveRef.current = content;
        return;
      }
      try {
        savingRef.current = true;
        setSaving(true);
        await fetch('/api/project/script?file=tts', {
          method: 'POST',
          headers: { 'Content-Type': 'text/plain' },
          body: content,
        });
        setTtsExists(Boolean(content.trim()));
      } finally {
        savingRef.current = false;
        setSaving(false);
        if (pendingSaveRef.current !== null) {
          const queued = pendingSaveRef.current;
          pendingSaveRef.current = null;
          saveTtsScript(queued);
        }
      }
    },
    []
  );

  const handleEditorChange = (value: string) => {
    setTtsScript(value);
    if (debounceRef.current) clearTimeout(debounceRef.current);
    debounceRef.current = setTimeout(() => {
      saveTtsScript(value);
    }, 1000);
  };

  const handleEditorBlur = () => {
    if (debounceRef.current) clearTimeout(debounceRef.current);
    saveTtsScript(ttsScript);
  };

  const handleGenerate = async () => {
    if (generatingRef.current) return;
    generatingRef.current = true;
    setIsGenerating(true);
    setGenerateError(null);
    try {
      const res = await fetch('/api/pipeline/tts-script/run', { method: 'POST' });
      if (!res.ok) {
        setGenerateError(`Server error: ${res.status}`);
        return;
      }

      // The endpoint returns an SSE stream (text/event-stream), not JSON.
      // Read the stream and extract the jobId from the first event that has one.
      const reader = res.body?.getReader();
      if (!reader) return;

      const decoder = new TextDecoder();
      let buffer = '';
      let foundJobId = false;
      let isErrorEvent = false;

      while (!foundJobId) {
        const { done: streamDone, value } = await reader.read();
        if (streamDone) break;

        buffer += decoder.decode(value, { stream: true });
        const lines = buffer.split('\n');

        for (const line of lines) {
          // Detect SSE error events
          if (line === 'event: error') {
            isErrorEvent = true;
            continue;
          }

          if (!line.startsWith('data: ')) continue;
          try {
            const data = JSON.parse(line.slice(6));

            // If this is an error event, show the error message
            if (isErrorEvent) {
              setGenerateError(data?.message ?? 'Generation failed');
              foundJobId = true; // stop reading
              break;
            }

            if (data?.jobId) {
              setJobId(data.jobId);
              const ts = new Date().toISOString();
              localStorage.setItem(LAST_RUN_KEY, ts);
              setLastRunTime(ts);
              foundJobId = true;
              break;
            }
          } catch {
            // Not valid JSON yet, continue reading
          }
          isErrorEvent = false;
        }

        // Keep only the last incomplete line in the buffer
        if (!buffer.endsWith('\n')) {
          buffer = lines[lines.length - 1] ?? '';
        } else {
          buffer = '';
        }
      }

      // Release the reader — SseLogPanel will open its own stream
      reader.cancel().catch(() => {});
    } finally {
      generatingRef.current = false;
      setIsGenerating(false);
    }
  };

  const diffLinesComputed = useMemo(() => {
    const parts = diffLines(mainScript ?? '', ttsScript ?? '');
    const left: DiffLine[] = [];
    const right: DiffLine[] = [];

    for (const part of parts) {
      const lines = part.value.split('\n');
      if (lines[lines.length - 1] === '') lines.pop();

      for (const line of lines) {
        if (part.added) {
          left.push({ type: 'empty', text: '' });
          right.push({ type: 'added', text: line });
        } else if (part.removed) {
          left.push({ type: 'removed', text: line });
          right.push({ type: 'empty', text: '' });
        } else {
          left.push({ type: 'unchanged', text: line });
          right.push({ type: 'unchanged', text: line });
        }
      }
    }

    return { left, right };
  }, [mainScript, ttsScript]);

  const lineClass = (type: DiffLineType) => {
    switch (type) {
      case 'added':
        return 'text-green-400';
      case 'removed':
        return 'text-red-400';
      case 'unchanged':
        return 'text-gray-400';
      case 'empty':
      default:
        return 'text-transparent';
    }
  };

  return (
    <div className="w-full space-y-6">
      <h2 className="text-xl font-semibold">Stage 3 — TTS Script</h2>
      {/* Header */}
      <div className="flex items-center justify-between">
        <button
          onClick={handleGenerate}
          disabled={isGenerating}
          className={`px-4 py-2 rounded font-semibold transition ${
            isGenerating
              ? 'bg-gray-700 text-gray-400 cursor-not-allowed'
              : 'bg-blue-600 text-white hover:bg-blue-700'
          }`}
        >
          {isGenerating ? 'Generating…' : 'Generate TTS Script ↺'}
        </button>
        <span className="text-xs text-gray-400">
          Last run: {lastRunTime ? new Date(lastRunTime).toLocaleString() : '—'}
        </span>
      </div>

      {/* SSE Log */}
      <SseLogPanel jobId={jobId} onDone={loadScripts} />

      {/* Generation Error */}
      {generateError && (
        <div className="text-red-400 font-mono text-sm bg-red-900/20 p-3 rounded">
          Generation failed: {generateError}
        </div>
      )}

      {/* Diff View */}
      <div className="grid grid-cols-2 gap-4">
        <div>
          <div className="text-xs font-semibold text-gray-400 mb-1">main_script.md</div>
          <pre className="overflow-x-auto text-xs bg-black/20 p-2 rounded">
            {diffLinesComputed.left.map((line, idx) => (
              <div key={`left-${idx}`} className={lineClass(line.type)}>
                {line.text || ' '}
              </div>
            ))}
          </pre>
        </div>
        <div>
          <div className="text-xs font-semibold text-gray-400 mb-1">tts_script.md</div>
          <pre className="overflow-x-auto text-xs bg-black/20 p-2 rounded">
            {diffLinesComputed.right.map((line, idx) => (
              <div key={`right-${idx}`} className={lineClass(line.type)}>
                {line.text || ' '}
              </div>
            ))}
          </pre>
        </div>
      </div>

      {/* Editor */}
      <div className="space-y-2">
        <div className="text-xs font-semibold text-gray-400">Edit tts_script.md</div>
        <CodeMirror
          value={ttsScript}
          height="300px"
          extensions={[markdown()]}
          onChange={handleEditorChange}
          onBlur={handleEditorBlur}
          theme="dark"
        />
        {saving && <div className="text-xs text-gray-400">Saving…</div>}
      </div>

      {/* Advance */}
      <div className="flex justify-end">
        <button
          onClick={onAdvance}
          disabled={!ttsExists}
          className={`px-4 py-2 rounded font-semibold transition ${
            ttsExists
              ? 'bg-green-600 text-white hover:bg-green-700'
              : 'bg-gray-700 text-gray-400 cursor-not-allowed'
          }`}
        >
          Render Audio →
        </button>
      </div>
    </div>
  );
}