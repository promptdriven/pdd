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

  const debounceRef = useRef<NodeJS.Timeout | null>(null);

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
      if (saving) return;
      try {
        setSaving(true);
        await fetch('/api/project/script?file=tts', {
          method: 'POST',
          headers: { 'Content-Type': 'text/plain' },
          body: content,
        });
        setTtsExists(Boolean(content.trim()));
      } finally {
        setSaving(false);
      }
    },
    [saving]
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
    const res = await fetch('/api/pipeline/tts-script/run', { method: 'POST' });
    if (!res.ok) return;
    const data = await res.json();
    if (data?.jobId) {
      setJobId(data.jobId);
      const ts = new Date().toISOString();
      localStorage.setItem(LAST_RUN_KEY, ts);
      setLastRunTime(ts);
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
      {/* Header */}
      <div className="flex items-center justify-between">
        <button
          onClick={handleGenerate}
          className="px-4 py-2 rounded bg-blue-600 text-white font-semibold hover:bg-blue-700 transition"
        >
          Generate TTS Script ↺
        </button>
        <span className="text-xs text-gray-400">
          Last run: {lastRunTime ? new Date(lastRunTime).toLocaleString() : '—'}
        </span>
      </div>

      {/* SSE Log */}
      <SseLogPanel jobId={jobId} />

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