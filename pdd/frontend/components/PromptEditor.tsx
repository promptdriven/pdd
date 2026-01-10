import React, { useEffect, useRef, useState } from 'react';
import { EditorState } from '@codemirror/state';
import { EditorView, lineNumbers, highlightActiveLine, keymap } from '@codemirror/view';
import { defaultKeymap, history, historyKeymap } from '@codemirror/commands';
import { markdown } from '@codemirror/lang-markdown';
import { oneDark } from '@codemirror/theme-one-dark';
import { api } from '../api';

interface PromptEditorProps {
  promptPath: string;
  onSave?: () => void;
  onCancel?: () => void;
}

const PromptEditor: React.FC<PromptEditorProps> = ({ promptPath, onSave, onCancel }) => {
  const editorContainerRef = useRef<HTMLDivElement>(null);
  const editorViewRef = useRef<EditorView | null>(null);
  const originalContentRef = useRef<string>('');

  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [content, setContent] = useState<string | null>(null);
  const [hasChanges, setHasChanges] = useState(false);
  const [saving, setSaving] = useState(false);
  const [saveSuccess, setSaveSuccess] = useState(false);

  // Load file content
  useEffect(() => {
    let cancelled = false;

    const loadContent = async () => {
      setLoading(true);
      setError(null);
      try {
        const file = await api.getFileContent(promptPath);
        if (!cancelled) {
          originalContentRef.current = file.content;
          setContent(file.content);
        }
      } catch (e: any) {
        if (!cancelled) {
          setError(e.message || 'Failed to load file');
        }
      } finally {
        if (!cancelled) {
          setLoading(false);
        }
      }
    };

    loadContent();

    return () => {
      cancelled = true;
    };
  }, [promptPath]);

  // Initialize editor after content is loaded and container is rendered
  useEffect(() => {
    if (content === null || !editorContainerRef.current) return;

    // Clean up existing editor
    if (editorViewRef.current) {
      editorViewRef.current.destroy();
      editorViewRef.current = null;
    }

    const state = EditorState.create({
      doc: content,
      extensions: [
        lineNumbers(),
        highlightActiveLine(),
        history(),
        keymap.of([...defaultKeymap, ...historyKeymap]),
        markdown(),
        oneDark,
        EditorView.updateListener.of((update) => {
          if (update.docChanged) {
            const newContent = update.state.doc.toString();
            setHasChanges(newContent !== originalContentRef.current);
          }
        }),
        EditorView.theme({
          '&': {
            height: '350px',
            fontSize: '14px',
            backgroundColor: 'rgb(17 24 39)',
          },
          '.cm-scroller': {
            overflow: 'auto',
            fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace',
          },
          '.cm-gutters': {
            backgroundColor: 'rgb(31 41 55)',
            borderRight: '1px solid rgb(55 65 81)',
          },
          '.cm-activeLineGutter': {
            backgroundColor: 'rgb(55 65 81)',
          },
          '.cm-activeLine': {
            backgroundColor: 'rgba(55, 65, 81, 0.5)',
          },
        }),
      ],
    });

    editorViewRef.current = new EditorView({
      state,
      parent: editorContainerRef.current,
    });

    // Cleanup on unmount
    return () => {
      if (editorViewRef.current) {
        editorViewRef.current.destroy();
        editorViewRef.current = null;
      }
    };
  }, [content]);

  const handleSave = async () => {
    if (!editorViewRef.current) return;

    setSaving(true);
    setSaveSuccess(false);
    setError(null);

    try {
      const newContent = editorViewRef.current.state.doc.toString();
      await api.writeFile(promptPath, newContent);
      originalContentRef.current = newContent;
      setHasChanges(false);
      setSaveSuccess(true);

      setTimeout(() => {
        setSaveSuccess(false);
        onSave?.();
      }, 1000);
    } catch (e: any) {
      setError(e.message || 'Failed to save');
    } finally {
      setSaving(false);
    }
  };

  const handleCancel = () => {
    if (hasChanges && !window.confirm('Discard unsaved changes?')) return;
    onCancel?.();
  };

  const handleRetry = () => {
    setContent(null);
    setError(null);
    setLoading(true);
    api.getFileContent(promptPath)
      .then(file => {
        originalContentRef.current = file.content;
        setContent(file.content);
      })
      .catch(e => setError(e.message || 'Failed to load file'))
      .finally(() => setLoading(false));
  };

  if (loading) {
    return (
      <div className="border-t border-gray-700 bg-gray-900/50 p-6">
        <div className="flex items-center gap-2 text-gray-400">
          <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
            <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
            <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
          </svg>
          Loading prompt...
        </div>
      </div>
    );
  }

  if (error && content === null) {
    return (
      <div className="border-t border-gray-700 bg-gray-900/50 p-6">
        <div className="text-red-400 mb-2">Error: {error}</div>
        <button
          onClick={handleRetry}
          className="text-blue-400 hover:text-blue-300 underline text-sm"
        >
          Retry
        </button>
      </div>
    );
  }

  return (
    <div className="border-t border-gray-700 bg-gray-900/50">
      {/* Editor header */}
      <div className="flex items-center justify-between px-4 py-2 border-b border-gray-700 bg-gray-800/50">
        <div className="flex items-center gap-2 text-sm text-gray-400">
          <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M11 5H6a2 2 0 00-2 2v11a2 2 0 002 2h11a2 2 0 002-2v-5m-1.414-9.414a2 2 0 112.828 2.828L11.828 15H9v-2.828l8.586-8.586z" />
          </svg>
          <span className="font-mono">{promptPath}</span>
        </div>
        {hasChanges && (
          <span className="text-yellow-400 text-sm flex items-center gap-1">
            <span className="w-2 h-2 bg-yellow-400 rounded-full"></span>
            Unsaved changes
          </span>
        )}
      </div>

      {/* Editor container */}
      <div ref={editorContainerRef} className="codemirror-container" />

      {/* Error message */}
      {error && (
        <div className="px-4 py-2 bg-red-900/30 border-t border-red-700 text-red-300 text-sm">
          {error}
        </div>
      )}

      {/* Footer with save/cancel */}
      <div className="flex items-center justify-between px-4 py-3 border-t border-gray-700 bg-gray-800/30">
        <div className="text-sm">
          {saveSuccess && (
            <span className="text-green-400 flex items-center gap-1">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
              Saved!
            </span>
          )}
        </div>
        <div className="flex gap-2">
          <button
            onClick={handleCancel}
            className="px-4 py-1.5 text-sm text-gray-300 hover:text-white hover:bg-gray-700 rounded transition-colors"
          >
            Cancel
          </button>
          <button
            onClick={handleSave}
            disabled={!hasChanges || saving}
            className={`px-4 py-1.5 text-sm rounded flex items-center gap-2 transition-colors ${
              hasChanges && !saving
                ? 'bg-blue-600 text-white hover:bg-blue-500'
                : 'bg-gray-700 text-gray-500 cursor-not-allowed'
            }`}
          >
            {saving ? (
              <>
                <svg className="animate-spin h-4 w-4" viewBox="0 0 24 24">
                  <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" fill="none" />
                  <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                </svg>
                Saving...
              </>
            ) : (
              <>
                <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 7H5a2 2 0 00-2 2v9a2 2 0 002 2h14a2 2 0 002-2V9a2 2 0 00-2-2h-3m-1 4l-3 3m0 0l-3-3m3 3V4" />
                </svg>
                Save
              </>
            )}
          </button>
        </div>
      </div>
    </div>
  );
};

export default PromptEditor;
