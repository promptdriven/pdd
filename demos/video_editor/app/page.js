'use client';

import { useState, useEffect, useRef, useCallback } from 'react';
import Script from 'next/script';

// ============================================================================
// API Client
// ============================================================================

const api = {
  async getSections() { return (await fetch('/api/sections')).json(); },
  async getAnnotations() { return (await fetch('/api/annotations')).json(); },
  async createAnnotation(ann) {
    return (await fetch('/api/annotations', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(ann) })).json();
  },
  async updateAnnotation(id, data) {
    return (await fetch(`/api/annotations/${id}`, { method: 'PUT', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(data) })).json();
  },
  async deleteAnnotation(id) {
    return fetch(`/api/annotations/${id}`, { method: 'DELETE' });
  },
  async analyzeAnnotation(id) {
    return (await fetch(`/api/annotations/${id}/analyze`, { method: 'POST' })).json();
  },
  async analyze(text, sectionId, timestamp) {
    return (await fetch('/api/analyze', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ text, sectionId, timestamp }) })).json();
  },
  async uploadThumbnail(dataUrl) {
    return (await fetch('/api/thumbnails', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ dataUrl }) })).json();
  },
  async resolveBatch(sectionId) {
    return (await fetch(`/api/sections/${sectionId}/resolve-batch`, { method: 'POST' })).json();
  },
  async getJob(id) { return (await fetch(`/api/jobs/${id}`)).json(); },
  streamJob(id, onEvent) {
    const es = new EventSource(`/api/jobs/${id}/stream`);
    es.addEventListener('progress', e => onEvent('progress', JSON.parse(e.data)));
    es.addEventListener('done', e => { onEvent('done', JSON.parse(e.data)); es.close(); });
    es.addEventListener('error', e => {
      try { onEvent('error', JSON.parse(e.data)); } catch { onEvent('error', {}); }
      es.close();
    });
    return es;
  },
  async getPipelineStatus() { return (await fetch('/api/pipeline/status')).json(); },
  async runPipelineStage(stage, body = {}) {
    return (await fetch(`/api/pipeline/${stage}/run`, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) })).json();
  },
  async getProject() { return (await fetch('/api/project')).json(); },
  async updateProject(data) {
    return (await fetch('/api/project', { method: 'PUT', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(data) })).json();
  },
  async getScript() { return (await fetch('/api/project/script')).json(); },
  async saveScript(content) {
    return (await fetch('/api/project/script', { method: 'PUT', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ content }) })).json();
  },
};

// ============================================================================
// Pipeline Sidebar
// ============================================================================

const STAGES = [
  { id: 'project-setup', label: '1 · Project Setup', num: 1 },
  { id: 'script-editor', label: '2 · Script Editor', num: 2 },
  { id: 'tts-script', label: '3 · TTS Script', num: 3 },
  { id: 'tts-render', label: '4 · TTS Rendering', num: 4 },
  { id: 'audio-sync', label: '5 · Audio Sync', num: 5 },
  { id: 'specs', label: '6 · Spec Generation', num: 6 },
  { id: 'veo', label: '7 · Veo Generation', num: 7 },
  { id: 'compositions', label: '8 · Compositions', num: 8 },
  { id: 'render', label: '9 · Render + Stitch', num: 9 },
  { id: 'audit', label: '10 · Audit', num: 10 },
];

function PipelineSidebar({ activeView, setActiveView, stageStatuses }) {
  return (
    <nav className="pipeline-sidebar">
      <div className="sidebar-header">Pipeline</div>
      <div className="sidebar-stages">
        {STAGES.map(stage => (
          <div
            key={stage.id}
            className={`stage-item ${activeView === stage.id ? 'active' : ''}`}
            onClick={() => setActiveView(stage.id)}
          >
            <span className={`stage-badge ${stageStatuses[stage.id] || 'not_started'}`} />
            {stage.label}
          </div>
        ))}
        <div className="sidebar-divider" />
        <div
          className={`stage-item ${activeView === 'review' ? 'active' : ''}`}
          onClick={() => setActiveView('review')}
        >
          <span className="stage-badge done" style={{ background: 'var(--accent)' }} />
          Review
        </div>
      </div>
    </nav>
  );
}

// ============================================================================
// Pipeline Stage Panels
// ============================================================================

function PipelineStagePanel({ stageId, stageStatuses }) {
  const [log, setLog] = useState([]);
  const [running, setRunning] = useState(false);
  const stageConfig = STAGES.find(s => s.id === stageId);

  const runStage = async () => {
    setRunning(true);
    setLog([`[${new Date().toLocaleTimeString()}] Starting ${stageConfig.label}...`]);
    try {
      const { jobId } = await api.runPipelineStage(stageId);
      api.streamJob(jobId, (event, data) => {
        if (event === 'progress') {
          setLog(prev => [...prev, `[${new Date().toLocaleTimeString()}] Progress: ${data.progress}%`]);
        } else if (event === 'done') {
          setLog(prev => [...prev, `[${new Date().toLocaleTimeString()}] Done`]);
          setRunning(false);
        } else if (event === 'error') {
          setLog(prev => [...prev, `[${new Date().toLocaleTimeString()}] Error: ${data.error || 'Unknown error'}`]);
          setRunning(false);
        }
      });
    } catch (err) {
      setLog(prev => [...prev, `Error: ${err.message}`]);
      setRunning(false);
    }
  };

  return (
    <div className="pipeline-panel">
      <h2>{stageConfig?.label || stageId}</h2>
      <div className="panel-actions">
        <button className="btn btn-analyze" onClick={runStage} disabled={running}>
          {running ? 'Running...' : `Run ${stageConfig?.label.split('·')[1]?.trim() || stageId}`}
        </button>
      </div>
      {log.length > 0 && (
        <div className="progress-log">
          {log.map((line, i) => (
            <div key={i} className={`log-line ${line.includes('Done') ? 'success' : line.includes('Error') ? 'error-msg' : ''}`}>
              {line}
            </div>
          ))}
        </div>
      )}
      <p style={{ color: 'var(--text-muted)', fontSize: 13 }}>
        Status: {stageStatuses[stageId] || 'not_started'}
      </p>
    </div>
  );
}

// ============================================================================
// Script Editor Panel (Stage 2)
// ============================================================================

function parseScriptBlocks(text) {
  if (!text) return [];
  const lines = text.split('\n');
  const blocks = [];
  let i = 0;

  while (i < lines.length) {
    const line = lines[i];

    if (/^##\s+/.test(line)) {
      blocks.push({ type: 'section', text: line.replace(/^##\s+/, '') });
      i++;
    } else if (/^NARRATOR:\s*/.test(line)) {
      blocks.push({ type: 'narrator', text: line.replace(/^NARRATOR:\s*/, '') });
      i++;
    } else if (/^\[VISUAL:\s*/.test(line)) {
      let content = line;
      while (i + 1 < lines.length && !content.includes(']')) {
        i++;
        content += '\n' + lines[i];
      }
      blocks.push({ type: 'visual', text: content.replace(/^\[VISUAL:\s*/, '').replace(/\]$/, '') });
      i++;
    } else if (line.trim() === '') {
      i++;
    } else {
      blocks.push({ type: 'text', text: line });
      i++;
    }
  }

  return blocks;
}

function ScriptEditorPanel({ stageStatuses, setActiveView }) {
  const editorRef = useRef(null);
  const viewRef = useRef(null);
  const [content, setContent] = useState('');
  const [previewBlocks, setPreviewBlocks] = useState([]);
  const [saveStatus, setSaveStatus] = useState(null);
  const [splitRatio, setSplitRatio] = useState(0.5);
  const [running, setRunning] = useState(false);
  const [log, setLog] = useState([]);
  const saveTimerRef = useRef(null);
  const previewTimerRef = useRef(null);
  const isDraggingRef = useRef(false);
  const splitContainerRef = useRef(null);

  const hasNarrator = previewBlocks.some(b => b.type === 'narrator');

  // Load script and init CodeMirror
  useEffect(() => {
    let destroyed = false;

    async function init() {
      const data = await api.getScript().catch(() => ({ content: '' }));
      if (destroyed) return;
      const initialContent = data.content || '';
      setContent(initialContent);
      setPreviewBlocks(parseScriptBlocks(initialContent));

      const { EditorView, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter } = await import('@codemirror/view');
      const { EditorState } = await import('@codemirror/state');
      const { markdown } = await import('@codemirror/lang-markdown');
      const { oneDark } = await import('@codemirror/theme-one-dark');
      const { defaultKeymap, history, historyKeymap } = await import('@codemirror/commands');
      const { syntaxHighlighting, defaultHighlightStyle } = await import('@codemirror/language');

      if (destroyed || !editorRef.current) return;

      const updateListener = EditorView.updateListener.of(update => {
        if (update.docChanged) {
          const doc = update.state.doc.toString();
          setContent(doc);
        }
      });

      const state = EditorState.create({
        doc: initialContent,
        extensions: [
          lineNumbers(),
          highlightActiveLine(),
          highlightActiveLineGutter(),
          history(),
          markdown(),
          oneDark,
          syntaxHighlighting(defaultHighlightStyle),
          keymap.of([...defaultKeymap, ...historyKeymap]),
          updateListener,
          EditorView.lineWrapping,
          EditorView.theme({
            '&': { height: '100%', fontSize: '13px' },
            '.cm-scroller': { overflow: 'auto', fontFamily: "'SF Mono', 'Fira Code', monospace" },
            '.cm-content': { padding: '12px 0' },
          }),
        ],
      });

      viewRef.current = new EditorView({ state, parent: editorRef.current });
    }

    init();

    return () => {
      destroyed = true;
      if (viewRef.current) {
        viewRef.current.destroy();
        viewRef.current = null;
      }
    };
  }, []);

  // Auto-save on 1s debounce
  useEffect(() => {
    if (saveTimerRef.current) clearTimeout(saveTimerRef.current);
    if (content === '' && !viewRef.current) return; // skip initial empty state

    saveTimerRef.current = setTimeout(async () => {
      setSaveStatus('saving');
      try {
        await api.saveScript(content);
        setSaveStatus('saved');
      } catch {
        setSaveStatus('error');
      }
    }, 1000);

    return () => { if (saveTimerRef.current) clearTimeout(saveTimerRef.current); };
  }, [content]);

  // Preview parse on 200ms debounce
  useEffect(() => {
    if (previewTimerRef.current) clearTimeout(previewTimerRef.current);
    previewTimerRef.current = setTimeout(() => {
      setPreviewBlocks(parseScriptBlocks(content));
    }, 200);
    return () => { if (previewTimerRef.current) clearTimeout(previewTimerRef.current); };
  }, [content]);

  // Resizable split divider
  const onDividerPointerDown = useCallback((e) => {
    e.preventDefault();
    isDraggingRef.current = true;

    const onMove = (me) => {
      if (!isDraggingRef.current || !splitContainerRef.current) return;
      const rect = splitContainerRef.current.getBoundingClientRect();
      const ratio = Math.min(0.8, Math.max(0.2, (me.clientX - rect.left) / rect.width));
      setSplitRatio(ratio);
    };

    const onUp = () => {
      isDraggingRef.current = false;
      document.removeEventListener('pointermove', onMove);
      document.removeEventListener('pointerup', onUp);
    };

    document.addEventListener('pointermove', onMove);
    document.addEventListener('pointerup', onUp);
  }, []);

  const runTtsScript = async () => {
    setRunning(true);
    setLog([`[${new Date().toLocaleTimeString()}] Starting TTS Script generation...`]);
    try {
      const { jobId } = await api.runPipelineStage('tts-script');
      api.streamJob(jobId, (event, data) => {
        if (event === 'progress') {
          setLog(prev => [...prev, `[${new Date().toLocaleTimeString()}] Progress: ${data.progress}%`]);
        } else if (event === 'done') {
          setLog(prev => [...prev, `[${new Date().toLocaleTimeString()}] Done`]);
          setRunning(false);
          setActiveView('tts-script');
        } else if (event === 'error') {
          setLog(prev => [...prev, `[${new Date().toLocaleTimeString()}] Error: ${data.error || 'Unknown error'}`]);
          setRunning(false);
        }
      });
    } catch (err) {
      setLog(prev => [...prev, `Error: ${err.message}`]);
      setRunning(false);
    }
  };

  return (
    <div className="script-editor-panel">
      <div className="script-editor-header">
        <div className="script-editor-title">
          <h2>Stage 2 — Script Editor</h2>
          <span className="save-indicator">
            {saveStatus === 'saving' && 'Saving...'}
            {saveStatus === 'saved' && 'Saved'}
            {saveStatus === 'error' && 'Save failed'}
          </span>
        </div>
        <button
          className="btn btn-analyze"
          onClick={runTtsScript}
          disabled={running || !hasNarrator}
          title={!hasNarrator ? 'Add at least one NARRATOR: line to enable' : ''}
        >
          {running ? 'Generating...' : 'Generate TTS Script →'}
        </button>
      </div>

      {log.length > 0 && (
        <div className="progress-log" style={{ margin: '0 16px 8px' }}>
          {log.map((line, i) => (
            <div key={i} className={`log-line ${line.includes('Done') ? 'success' : line.includes('Error') ? 'error-msg' : ''}`}>
              {line}
            </div>
          ))}
        </div>
      )}

      <div className="script-editor-split" ref={splitContainerRef}>
        <div className="script-editor-left" style={{ flex: `0 0 ${splitRatio * 100}%` }}>
          <div ref={editorRef} className="script-editor-cm" />
        </div>
        <div className="script-editor-divider" onPointerDown={onDividerPointerDown} />
        <div className="script-editor-right" style={{ flex: `0 0 ${(1 - splitRatio) * 100 - 0.3}%` }}>
          <div className="preview-header">Structured Preview</div>
          <div className="preview-blocks">
            {previewBlocks.length === 0 && (
              <div className="preview-empty">
                Start typing in the editor to see a structured preview.
                <br /><br />
                Supported formats:<br />
                <code>## Section Name</code> — section header<br />
                <code>NARRATOR: text</code> — narration line<br />
                <code>[VISUAL: description]</code> — visual cue
              </div>
            )}
            {previewBlocks.map((block, i) => (
              <div key={i} className={`preview-block preview-block-${block.type}`}>
                <span className={`preview-badge badge-${block.type}`}>
                  {block.type === 'section' && 'SECTION'}
                  {block.type === 'narrator' && 'NARRATOR'}
                  {block.type === 'visual' && 'VISUAL'}
                  {block.type === 'text' && 'TEXT'}
                </span>
                <span className="preview-block-text">{block.text}</span>
              </div>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
}

// ============================================================================
// Video Player Component
// ============================================================================

function VideoPlayer({ sections, currentSection, setCurrentSection, videoRef, onTimeUpdate }) {
  const [playing, setPlaying] = useState(false);
  const [currentTime, setCurrentTime] = useState(0);
  const [duration, setDuration] = useState(0);
  const seekRef = useRef(null);

  const videoSrc = currentSection === 'full'
    ? '/api/video/full'
    : `/api/video/sections/${sections.find(s => s.id === currentSection)?.videoFile || ''}`;

  const formatTime = (t) => {
    const m = Math.floor(t / 60).toString().padStart(2, '0');
    const s = (t % 60).toFixed(1).padStart(4, '0');
    return `${m}:${s}`;
  };

  const togglePlay = useCallback(() => {
    if (!videoRef.current) return;
    if (videoRef.current.paused) { videoRef.current.play(); setPlaying(true); }
    else { videoRef.current.pause(); setPlaying(false); }
  }, [videoRef]);

  useEffect(() => {
    const vid = videoRef.current;
    if (!vid) return;
    const onTime = () => { setCurrentTime(vid.currentTime); onTimeUpdate?.(vid.currentTime); };
    const onDur = () => setDuration(vid.duration || 0);
    const onPlay = () => setPlaying(true);
    const onPause = () => setPlaying(false);
    vid.addEventListener('timeupdate', onTime);
    vid.addEventListener('loadedmetadata', onDur);
    vid.addEventListener('play', onPlay);
    vid.addEventListener('pause', onPause);
    return () => { vid.removeEventListener('timeupdate', onTime); vid.removeEventListener('loadedmetadata', onDur); vid.removeEventListener('play', onPlay); vid.removeEventListener('pause', onPause); };
  }, [videoRef, onTimeUpdate]);

  const onSeek = (e) => {
    if (videoRef.current && duration > 0) {
      videoRef.current.currentTime = (e.target.value / 100) * duration;
    }
  };

  return (
    <section className="video-area">
      <div className="video-container" id="video-container">
        <video ref={videoRef} preload="metadata" src={videoSrc} key={videoSrc} />
        <canvas id="draw-canvas" />
      </div>
      <div className="video-controls">
        <button className="ctrl-btn" onClick={togglePlay}>{playing ? 'Pause' : 'Play'}</button>
        <input
          type="range" className="seek-bar" min="0" max="100" step="0.1"
          value={duration > 0 ? (currentTime / duration) * 100 : 0}
          onChange={onSeek} ref={seekRef}
        />
        <span className="time-display">{formatTime(currentTime)} / {formatTime(duration)}</span>
        <select value={currentSection} onChange={e => setCurrentSection(e.target.value)}>
          <option value="full">Full Video</option>
          {sections.map(s => <option key={s.id} value={s.id}>{s.label}</option>)}
        </select>
        <select defaultValue="1" onChange={e => { if (videoRef.current) videoRef.current.playbackRate = parseFloat(e.target.value); }}>
          <option value="0.25">0.25x</option>
          <option value="0.5">0.5x</option>
          <option value="1">1x</option>
          <option value="1.5">1.5x</option>
          <option value="2">2x</option>
        </select>
      </div>
    </section>
  );
}

// ============================================================================
// Annotation Panel Component
// ============================================================================

function AnnotationPanel({ sections, annotations, setAnnotations, videoRef, currentSection }) {
  const [filterSection, setFilterSection] = useState('');
  const [filterSeverity, setFilterSeverity] = useState('');
  const [hideResolved, setHideResolved] = useState(false);
  const [text, setText] = useState('');
  const [analyzing, setAnalyzing] = useState(false);
  const [analysisResult, setAnalysisResult] = useState(null);
  const [editingId, setEditingId] = useState(null);

  const filtered = (annotations || []).filter(a => {
    if (filterSection && a.video?.sectionId !== filterSection) return false;
    if (filterSeverity && a.analysis?.severity !== filterSeverity) return false;
    if (hideResolved && a.resolved) return false;
    return true;
  });

  const pendingBySectionCount = {};
  for (const ann of (annotations || [])) {
    if (ann.analysis?.status === 'completed' && !ann.resolved && ann.video?.sectionId) {
      pendingBySectionCount[ann.video.sectionId] = (pendingBySectionCount[ann.video.sectionId] || 0) + 1;
    }
  }

  const saveAnnotation = async () => {
    if (!text.trim()) return;
    const sectionId = currentSection === 'full' ? (sections[0]?.id || '') : currentSection;
    const timestamp = videoRef.current?.currentTime || 0;

    if (editingId) {
      const updated = await api.updateAnnotation(editingId, { text: { content: text, inputMethod: 'typed' } });
      setAnnotations(prev => prev.map(a => a.id === editingId ? updated : a));
      setEditingId(null);
    } else {
      const ann = await api.createAnnotation({
        video: { source: currentSection === 'full' ? 'full' : 'section', sectionId, timestamp, timestampFormatted: formatTime(timestamp) },
        text: { content: text, inputMethod: 'typed' },
        drawing: null,
        analysis: { status: 'pending' },
        resolved: false,
      });
      setAnnotations(prev => [...prev, ann]);
    }
    setText('');
    setAnalysisResult(null);
  };

  const analyzeText = async () => {
    if (!text.trim()) return;
    setAnalyzing(true);
    setAnalysisResult(null);
    try {
      const sectionId = currentSection === 'full' ? (sections[0]?.id || '') : currentSection;
      const result = await api.analyze(text, sectionId, formatTime(videoRef.current?.currentTime || 0));
      setAnalysisResult(result);
    } catch (err) {
      setAnalysisResult({ error: err.message });
    }
    setAnalyzing(false);
  };

  const analyzeAnnotation = async (id) => {
    const result = await api.analyzeAnnotation(id);
    setAnnotations(prev => prev.map(a => a.id === id ? result : a));
  };

  const deleteAnnotation = async (id) => {
    await api.deleteAnnotation(id);
    setAnnotations(prev => prev.filter(a => a.id !== id));
  };

  const resolveBatch = async (sectionId) => {
    try {
      const { jobId } = await api.resolveBatch(sectionId);
      api.streamJob(jobId, (event, data) => {
        if (event === 'done') {
          // Reload annotations to get updated state
          api.getAnnotations().then(d => setAnnotations(d.annotations || []));
        }
      });
    } catch (err) {
      console.error('Batch resolve error:', err);
    }
  };

  const formatTime = (t) => {
    const m = Math.floor(t / 60).toString().padStart(2, '0');
    const s = (t % 60).toFixed(1).padStart(4, '0');
    return `${m}:${s}`;
  };

  return (
    <aside className="annotation-panel">
      <div className="panel-header">
        <h2>Annotations</h2>
        <div className="panel-filters">
          <select value={filterSection} onChange={e => setFilterSection(e.target.value)}>
            <option value="">All Sections</option>
            {sections.map(s => <option key={s.id} value={s.id}>{s.label}</option>)}
          </select>
          <select value={filterSeverity} onChange={e => setFilterSeverity(e.target.value)}>
            <option value="">All Severities</option>
            <option value="critical">Critical</option>
            <option value="high">High</option>
            <option value="medium">Medium</option>
            <option value="low">Low</option>
            <option value="informational">Info</option>
          </select>
          <label className="filter-resolved">
            <input type="checkbox" checked={hideResolved} onChange={e => setHideResolved(e.target.checked)} />
            Hide resolved
          </label>
        </div>
      </div>

      <div className="annotation-list">
        {filtered.map(ann => (
          <div key={ann.id} className={`annotation-item ${ann.resolved ? 'resolved' : ''}`}
            onClick={() => { if (videoRef.current && ann.video?.timestamp) videoRef.current.currentTime = ann.video.timestamp; }}>
            <div className="ann-header">
              <span className="ann-time">{ann.video?.timestampFormatted || '—'}</span>
              <span style={{ display: 'flex', gap: 4 }}>
                {ann.analysis?.fixType && <span className={`fix-type-badge ${ann.analysis.fixType}`}>{ann.analysis.fixType}</span>}
                {ann.analysis?.severity && <span className={`severity-badge ${ann.analysis.severity}`}>{ann.analysis.severity}</span>}
              </span>
            </div>
            <div className="ann-text">{ann.analysis?.summary || ann.text?.content || '(no text)'}</div>
            {ann.resolveJob && <div className="ann-status">Job: {ann.resolveJob.status} {ann.resolveJob.step && `(${ann.resolveJob.step})`}</div>}
            <div className="ann-actions" onClick={e => e.stopPropagation()}>
              {ann.analysis?.status !== 'completed' && (
                <button onClick={() => analyzeAnnotation(ann.id)}>Analyze</button>
              )}
              <button onClick={() => { setEditingId(ann.id); setText(ann.text?.content || ''); }}>Edit</button>
              <button onClick={() => deleteAnnotation(ann.id)}>Delete</button>
            </div>
          </div>
        ))}
        {filtered.length === 0 && (
          <div style={{ padding: 20, textAlign: 'center', color: 'var(--text-muted)', fontSize: 13 }}>
            No annotations. Press Space to annotate.
          </div>
        )}
      </div>

      {/* Batch resolve bar */}
      {Object.entries(pendingBySectionCount).map(([secId, count]) => (
        <div key={secId} className="batch-resolve-bar">
          <span style={{ fontSize: 12, color: 'var(--text-secondary)' }}>
            {sections.find(s => s.id === secId)?.label || secId}: {count} pending
          </span>
          <button onClick={() => resolveBatch(secId)}>Apply {count} Fix{count > 1 ? 'es' : ''}</button>
        </div>
      ))}

      <div className="new-annotation">
        <h3>{editingId ? 'Edit Annotation' : 'New Annotation'}</h3>
        <textarea
          value={text}
          onChange={e => setText(e.target.value)}
          placeholder="Describe the issue..."
          rows={3}
        />
        <div className="form-actions">
          <button className="btn btn-analyze" onClick={analyzeText} disabled={analyzing || !text.trim()}>
            {analyzing ? 'Analyzing...' : 'Analyze with Claude'}
          </button>
          <button className="btn btn-save" onClick={saveAnnotation} disabled={!text.trim()}>
            {editingId ? 'Update' : 'Save'}
          </button>
          {editingId && <button className="btn" onClick={() => { setEditingId(null); setText(''); }}>Cancel</button>}
        </div>
        {analysisResult && (
          <div className="analysis-result">
            {analysisResult.error
              ? <div className="error-msg">Error: {analysisResult.error}</div>
              : <>
                  <div><strong>Severity:</strong> {analysisResult.severity} | <strong>Category:</strong> {analysisResult.category}</div>
                  <div><strong>Fix Type:</strong> {analysisResult.fixType}</div>
                  <div><strong>Summary:</strong> {analysisResult.summary}</div>
                  <div><strong>Assessment:</strong> {analysisResult.technicalAssessment}</div>
                </>
            }
          </div>
        )}
      </div>
    </aside>
  );
}

// ============================================================================
// Drawing Canvas (imperative — uses refs)
// ============================================================================

function useCanvasOverlay(videoRef, drawingActive) {
  const canvasRef = useRef(null);
  const pathsRef = useRef([]);
  const drawingRef = useRef(false);
  const toolRef = useRef('freehand');
  const colorRef = useRef('#ff4444');
  const strokeRef = useRef(4);
  const startRef = useRef(null);

  useEffect(() => {
    const canvas = document.getElementById('draw-canvas');
    if (!canvas) return;
    canvasRef.current = canvas;

    const resize = () => {
      const container = canvas.parentElement;
      if (container) {
        canvas.width = 1920;
        canvas.height = 1080;
        canvas.style.width = container.clientWidth + 'px';
        canvas.style.height = container.clientHeight + 'px';
        redraw();
      }
    };

    const getPos = (e) => {
      const rect = canvas.getBoundingClientRect();
      return {
        x: ((e.clientX - rect.left) / rect.width) * 1920,
        y: ((e.clientY - rect.top) / rect.height) * 1080,
      };
    };

    const onDown = (e) => {
      if (!drawingActive.current) return;
      drawingRef.current = true;
      const pos = getPos(e);
      startRef.current = pos;

      if (toolRef.current === 'freehand') {
        pathsRef.current.push({ tool: 'freehand', color: colorRef.current, strokeWidth: strokeRef.current, points: [pos] });
      }
    };

    const onMove = (e) => {
      if (!drawingRef.current || !drawingActive.current) return;
      const pos = getPos(e);
      if (toolRef.current === 'freehand') {
        const current = pathsRef.current[pathsRef.current.length - 1];
        if (current) { current.points.push(pos); redraw(); }
      } else {
        redraw();
        // Preview shape
        const ctx = canvas.getContext('2d');
        ctx.strokeStyle = colorRef.current;
        ctx.lineWidth = strokeRef.current;
        const s = startRef.current;
        if (toolRef.current === 'rectangle') {
          ctx.strokeRect(s.x, s.y, pos.x - s.x, pos.y - s.y);
        } else if (toolRef.current === 'circle') {
          const rx = Math.abs(pos.x - s.x) / 2;
          const ry = Math.abs(pos.y - s.y) / 2;
          ctx.beginPath();
          ctx.ellipse(s.x + (pos.x - s.x) / 2, s.y + (pos.y - s.y) / 2, rx, ry, 0, 0, Math.PI * 2);
          ctx.stroke();
        } else if (toolRef.current === 'arrow') {
          ctx.beginPath();
          ctx.moveTo(s.x, s.y);
          ctx.lineTo(pos.x, pos.y);
          ctx.stroke();
          const angle = Math.atan2(pos.y - s.y, pos.x - s.x);
          const headLen = 20;
          ctx.beginPath();
          ctx.moveTo(pos.x, pos.y);
          ctx.lineTo(pos.x - headLen * Math.cos(angle - 0.4), pos.y - headLen * Math.sin(angle - 0.4));
          ctx.moveTo(pos.x, pos.y);
          ctx.lineTo(pos.x - headLen * Math.cos(angle + 0.4), pos.y - headLen * Math.sin(angle + 0.4));
          ctx.stroke();
        }
      }
    };

    const onUp = (e) => {
      if (!drawingRef.current || !drawingActive.current) return;
      drawingRef.current = false;
      const pos = getPos(e);
      const s = startRef.current;
      if (toolRef.current !== 'freehand' && toolRef.current !== 'text' && s) {
        pathsRef.current.push({
          tool: toolRef.current, color: colorRef.current, strokeWidth: strokeRef.current,
          startX: s.x, startY: s.y, endX: pos.x, endY: pos.y,
        });
      }
      redraw();
    };

    const redraw = () => {
      const ctx = canvas.getContext('2d');
      ctx.clearRect(0, 0, 1920, 1080);
      for (const p of pathsRef.current) {
        ctx.strokeStyle = p.color;
        ctx.lineWidth = p.strokeWidth;
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        if (p.tool === 'freehand' && p.points.length > 1) {
          ctx.beginPath();
          ctx.moveTo(p.points[0].x, p.points[0].y);
          for (let i = 1; i < p.points.length; i++) ctx.lineTo(p.points[i].x, p.points[i].y);
          ctx.stroke();
        } else if (p.tool === 'rectangle') {
          ctx.strokeRect(p.startX, p.startY, p.endX - p.startX, p.endY - p.startY);
        } else if (p.tool === 'circle') {
          const rx = Math.abs(p.endX - p.startX) / 2;
          const ry = Math.abs(p.endY - p.startY) / 2;
          ctx.beginPath();
          ctx.ellipse(p.startX + (p.endX - p.startX) / 2, p.startY + (p.endY - p.startY) / 2, rx, ry, 0, 0, Math.PI * 2);
          ctx.stroke();
        } else if (p.tool === 'arrow') {
          ctx.beginPath();
          ctx.moveTo(p.startX, p.startY);
          ctx.lineTo(p.endX, p.endY);
          ctx.stroke();
          const angle = Math.atan2(p.endY - p.startY, p.endX - p.startX);
          const headLen = 20;
          ctx.beginPath();
          ctx.moveTo(p.endX, p.endY);
          ctx.lineTo(p.endX - headLen * Math.cos(angle - 0.4), p.endY - headLen * Math.sin(angle - 0.4));
          ctx.moveTo(p.endX, p.endY);
          ctx.lineTo(p.endX - headLen * Math.cos(angle + 0.4), p.endY - headLen * Math.sin(angle + 0.4));
          ctx.stroke();
        } else if (p.tool === 'text' && p.text) {
          ctx.fillStyle = p.color;
          ctx.font = `${p.strokeWidth * 6}px sans-serif`;
          ctx.fillText(p.text, p.startX, p.startY);
        }
      }
    };

    canvas.addEventListener('pointerdown', onDown);
    canvas.addEventListener('pointermove', onMove);
    canvas.addEventListener('pointerup', onUp);
    window.addEventListener('resize', resize);
    resize();

    return () => {
      canvas.removeEventListener('pointerdown', onDown);
      canvas.removeEventListener('pointermove', onMove);
      canvas.removeEventListener('pointerup', onUp);
      window.removeEventListener('resize', resize);
    };
  }, [drawingActive]);

  return {
    setTool: (t) => { toolRef.current = t; },
    setColor: (c) => { colorRef.current = c; },
    setStrokeWidth: (w) => { strokeRef.current = w; },
    undo: () => { pathsRef.current.pop(); const ctx = canvasRef.current?.getContext('2d'); if (ctx) { ctx.clearRect(0, 0, 1920, 1080); } },
    clear: () => { pathsRef.current = []; const ctx = canvasRef.current?.getContext('2d'); if (ctx) { ctx.clearRect(0, 0, 1920, 1080); } },
    getPaths: () => pathsRef.current,
    captureComposite: (videoEl) => {
      const offscreen = document.createElement('canvas');
      offscreen.width = 1920;
      offscreen.height = 1080;
      const ctx = offscreen.getContext('2d');
      if (videoEl) ctx.drawImage(videoEl, 0, 0, 1920, 1080);
      if (canvasRef.current) ctx.drawImage(canvasRef.current, 0, 0);
      return offscreen.toDataURL('image/jpeg', 0.7);
    },
  };
}

// ============================================================================
// Main App
// ============================================================================

export default function Home() {
  const [activeView, setActiveView] = useState('review');
  const [sections, setSections] = useState([]);
  const [annotations, setAnnotations] = useState([]);
  const [stageStatuses, setStageStatuses] = useState({});
  const [currentSection, setCurrentSection] = useState('full');
  const [drawMode, setDrawMode] = useState(false);
  const [currentTool, setCurrentTool] = useState('freehand');
  const [annotateMode, setAnnotateMode] = useState(false);

  const videoRef = useRef(null);
  const drawingActiveRef = useRef(false);

  const canvas = useCanvasOverlay(videoRef, drawingActiveRef);

  // Toggle draw mode on canvas
  useEffect(() => {
    drawingActiveRef.current = drawMode;
    const el = document.getElementById('draw-canvas');
    if (el) {
      if (drawMode) el.classList.add('active');
      else el.classList.remove('active');
    }
  }, [drawMode]);

  // Load initial data
  useEffect(() => {
    api.getSections().then(setSections).catch(() => {});
    api.getAnnotations().then(d => setAnnotations(d.annotations || [])).catch(() => {});
    api.getPipelineStatus().then(d => setStageStatuses(d.stages || {})).catch(() => {});

    // Poll pipeline status
    const interval = setInterval(() => {
      api.getPipelineStatus().then(d => setStageStatuses(d.stages || {})).catch(() => {});
    }, 5000);
    return () => clearInterval(interval);
  }, []);

  // Keyboard shortcuts
  useEffect(() => {
    const onKey = (e) => {
      if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;

      if (e.code === 'Space') {
        e.preventDefault();
        if (!annotateMode) {
          // Enter annotate mode: pause + draw + mic
          if (videoRef.current && !videoRef.current.paused) videoRef.current.pause();
          setAnnotateMode(true);
          setDrawMode(true);
        } else {
          // Exit annotate mode: save and resume
          setAnnotateMode(false);
          setDrawMode(false);
          if (videoRef.current) videoRef.current.play();
        }
      } else if (e.code === 'KeyK') {
        if (videoRef.current) {
          if (videoRef.current.paused) videoRef.current.play();
          else videoRef.current.pause();
        }
      } else if (e.code === 'KeyD') {
        setDrawMode(prev => !prev);
      } else if (e.code === 'KeyF') { canvas.setTool('freehand'); setCurrentTool('freehand'); }
      else if (e.code === 'KeyR') { canvas.setTool('rectangle'); setCurrentTool('rectangle'); }
      else if (e.code === 'KeyC') { canvas.setTool('circle'); setCurrentTool('circle'); }
      else if (e.code === 'KeyA') { canvas.setTool('arrow'); setCurrentTool('arrow'); }
      else if (e.code === 'KeyT') { canvas.setTool('text'); setCurrentTool('text'); }
      else if (e.code === 'ArrowLeft') {
        if (videoRef.current) videoRef.current.currentTime = Math.max(0, videoRef.current.currentTime - 5);
      } else if (e.code === 'ArrowRight') {
        if (videoRef.current) videoRef.current.currentTime += 5;
      } else if (e.ctrlKey && e.code === 'KeyZ') {
        canvas.undo();
      } else if (e.code === 'Escape') {
        setAnnotateMode(false);
        setDrawMode(false);
      }
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [annotateMode, canvas]);

  const tools = [
    { id: 'freehand', label: 'F', title: 'Freehand (F)', icon: <svg width="16" height="16" viewBox="0 0 16 16"><path d="M2 14c2-4 4-6 6-8s4-3 6-4" stroke="currentColor" fill="none" strokeWidth="2" strokeLinecap="round"/></svg> },
    { id: 'rectangle', label: 'R', title: 'Rectangle (R)', icon: <svg width="16" height="16" viewBox="0 0 16 16"><rect x="2" y="3" width="12" height="10" stroke="currentColor" fill="none" strokeWidth="1.5"/></svg> },
    { id: 'circle', label: 'C', title: 'Circle (C)', icon: <svg width="16" height="16" viewBox="0 0 16 16"><circle cx="8" cy="8" r="6" stroke="currentColor" fill="none" strokeWidth="1.5"/></svg> },
    { id: 'arrow', label: 'A', title: 'Arrow (A)', icon: <svg width="16" height="16" viewBox="0 0 16 16"><line x1="2" y1="14" x2="14" y2="2" stroke="currentColor" strokeWidth="1.5"/><polyline points="8,2 14,2 14,8" stroke="currentColor" fill="none" strokeWidth="1.5"/></svg> },
    { id: 'text', label: 'T', title: 'Text (T)', icon: <svg width="16" height="16" viewBox="0 0 16 16"><text x="3" y="12" fontSize="12" fontWeight="bold" fill="currentColor">T</text></svg> },
  ];

  return (
    <div className="app-shell">
      <PipelineSidebar
        activeView={activeView}
        setActiveView={setActiveView}
        stageStatuses={stageStatuses}
      />

      <div className="main-content">
        {activeView === 'review' ? (
          <>
            <header className="toolbar">
              <div className="toolbar-left">
                <div style={{ display: 'flex', gap: 2 }}>
                  {tools.map(t => (
                    <button
                      key={t.id}
                      className={`tool-btn ${currentTool === t.id ? 'active' : ''}`}
                      title={t.title}
                      onClick={() => { canvas.setTool(t.id); setCurrentTool(t.id); }}
                    >
                      {t.icon}
                    </button>
                  ))}
                </div>
                <input type="color" defaultValue="#ff4444" onChange={e => canvas.setColor(e.target.value)} title="Drawing color" />
                <select defaultValue="4" onChange={e => canvas.setStrokeWidth(parseInt(e.target.value))}>
                  <option value="2">Thin</option>
                  <option value="4">Medium</option>
                  <option value="8">Thick</option>
                </select>
                <button className="toolbar-btn" onClick={() => canvas.undo()} title="Undo (Ctrl+Z)">Undo</button>
              </div>
              <div className="toolbar-right">
                <button
                  className={`toolbar-btn ${drawMode ? 'active' : ''}`}
                  onClick={() => setDrawMode(prev => !prev)}
                  title="Toggle Draw Mode (D)"
                >
                  {drawMode ? 'Drawing ON' : 'Draw Mode'}
                </button>
                {annotateMode && (
                  <span style={{ color: 'var(--accent)', fontSize: 12, fontWeight: 600 }}>
                    ANNOTATING — Press Space to save
                  </span>
                )}
              </div>
            </header>

            <div className="review-layout">
              <VideoPlayer
                sections={sections}
                currentSection={currentSection}
                setCurrentSection={setCurrentSection}
                videoRef={videoRef}
              />
              <AnnotationPanel
                sections={sections}
                annotations={annotations}
                setAnnotations={setAnnotations}
                videoRef={videoRef}
                currentSection={currentSection}
              />
            </div>
          </>
        ) : activeView === 'script-editor' ? (
          <ScriptEditorPanel stageStatuses={stageStatuses} setActiveView={setActiveView} />
        ) : (
          <PipelineStagePanel stageId={activeView} stageStatuses={stageStatuses} />
        )}
      </div>

      <div className="keyboard-hint">
        <kbd>Space</kbd> Annotate &nbsp; <kbd>K</kbd> Play/Pause &nbsp;
        <kbd>D</kbd> Draw &nbsp; <kbd>F</kbd><kbd>R</kbd><kbd>C</kbd><kbd>A</kbd><kbd>T</kbd> Tools &nbsp;
        <kbd>←</kbd><kbd>→</kbd> Seek &nbsp; <kbd>Ctrl+Z</kbd> Undo
      </div>
    </div>
  );
}
