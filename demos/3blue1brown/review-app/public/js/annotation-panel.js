/**
 * Annotation panel module - list, create, filter, and manage annotations.
 */
const AnnotationPanel = {
  annotations: [],
  listEl: null,
  currentAnalysis: null,
  editingId: null,

  init() {
    this.listEl = document.getElementById('annotation-list');
    this._bindEvents();
    this.load();
  },

  _bindEvents() {
    document.getElementById('analyze-btn').addEventListener('click', () => {
      if (this.editingId) {
        this._reanalyze();
      } else {
        this.analyze();
      }
    });
    document.getElementById('save-btn').addEventListener('click', () => this.save());
    document.getElementById('cancel-edit-btn').addEventListener('click', () => this.exitEditMode());
    document.getElementById('filter-section').addEventListener('change', () => this.renderList());
    document.getElementById('filter-severity').addEventListener('change', () => this.renderList());
    document.getElementById('filter-hide-resolved').addEventListener('change', () => this.renderList());
  },

  async load() {
    const data = await ApiClient.getAnnotations();
    this.annotations = data.annotations || [];
    this.renderList();
    this._reconnectActiveJobs();
  },

  _reconnectActiveJobs() {
    for (const ann of this.annotations) {
      if (ann.resolveJob && ann.resolveJob.jobId &&
          (ann.resolveJob.status === 'pending' || ann.resolveJob.status === 'running')) {
        // Check if job is still active, reconnect SSE
        ApiClient.getJob(ann.resolveJob.jobId).then(data => {
          if (data.status === 'done') {
            ann.resolved = true;
            ann.resolveJob = { jobId: ann.resolveJob.jobId, status: 'done' };
            this.renderList();
          } else if (data.status === 'error') {
            ann.resolveJob = { jobId: ann.resolveJob.jobId, status: 'error', error: data.error };
            this.renderList();
          } else {
            // Still running — reconnect SSE stream
            this._streamResolveJob(ann.id, ann.resolveJob.jobId);
          }
        }).catch(() => {
          // Job not found on server (server restarted) — mark as error
          ann.resolveJob = { jobId: ann.resolveJob.jobId, status: 'error', error: 'Job lost (server restarted)' };
          this.renderList();
        });
      }
    }
  },

  renderList() {
    const filterSection = document.getElementById('filter-section').value;
    const filterSeverity = document.getElementById('filter-severity').value;
    const hideResolved = document.getElementById('filter-hide-resolved').checked;

    let filtered = this.annotations;

    if (filterSection) {
      filtered = filtered.filter(a => a.video && a.video.sectionId === filterSection);
    }
    if (filterSeverity) {
      filtered = filtered.filter(a => a.analysis && a.analysis.severity === filterSeverity);
    }
    if (hideResolved) {
      filtered = filtered.filter(a => !a.resolved);
    }

    if (filtered.length === 0) {
      this.listEl.innerHTML = '<div class="empty-state">No annotations yet. Pause the video and add one.</div>';
      return;
    }

    this.listEl.innerHTML = filtered.map(a => this._renderItem(a)).join('');

    // Bind click handlers
    this.listEl.querySelectorAll('.annotation-item').forEach(el => {
      const id = el.dataset.id;
      el.addEventListener('click', (e) => {
        if (e.target.closest('.action-btn')) return;
        this._onItemClick(id);
      });
    });

    this.listEl.querySelectorAll('.action-btn[data-action="resolve"]').forEach(btn => {
      btn.addEventListener('click', () => this._toggleResolved(btn.dataset.id));
    });

    this.listEl.querySelectorAll('.action-btn[data-action="delete"]').forEach(btn => {
      btn.addEventListener('click', () => this._delete(btn.dataset.id));
    });
  },

  _renderItem(a) {
    const severity = a.analysis && a.analysis.severity ? a.analysis.severity : '';
    const isAnalyzing = a.analysis && a.analysis.status === 'analyzing';
    const severityBadge = isAnalyzing
      ? '<span class="severity-badge analyzing">Analyzing...</span>'
      : severity
        ? `<span class="severity-badge ${severity}">${severity}</span>`
        : '';
    const preview = a.text ? a.text.content : '';
    const ts = a.video ? a.video.timestampFormatted : '';
    const thumb = a.video && a.video.frameThumbnail
      ? `<img class="thumbnail" src="${a.video.frameThumbnail}" alt="frame">`
      : '<div class="thumbnail"></div>';
    const resolvedClass = a.resolved ? ' resolved' : '';
    const editingClass = a.id === this.editingId ? ' editing' : '';

    const resolveBtn = this._renderResolveButton(a);

    return `
      <div class="annotation-item${resolvedClass}${editingClass}" data-id="${a.id}">
        ${thumb}
        <div class="info">
          <div class="info-header">
            <span class="timestamp">${ts}</span>
            ${severityBadge}
          </div>
          <div class="preview">${this._escapeHtml(preview)}</div>
          <div class="actions">
            ${resolveBtn}
            <button class="action-btn" data-action="delete" data-id="${a.id}">Delete</button>
          </div>
        </div>
      </div>
    `;
  },

  _renderResolveButton(a) {
    const job = a.resolveJob;

    if (job && (job.status === 'pending')) {
      return `<button class="action-btn resolving" data-action="resolve" data-id="${a.id}" disabled>Queued...</button>`;
    }

    if (job && job.status === 'running') {
      const stepLabel = job.step === 'fixing' ? 'Fixing'
        : job.step === 'rendering' ? 'Rendering'
        : job.step === 'stitching' ? 'Stitching'
        : 'Working';
      const pct = typeof job.progress === 'number' ? ` ${job.progress}%` : '';
      return `<button class="action-btn resolving" data-action="resolve" data-id="${a.id}" disabled>${stepLabel}...${pct}</button>`;
    }

    if (job && job.status === 'error') {
      return `<button class="action-btn resolve-error" data-action="resolve" data-id="${a.id}" title="${this._escapeHtml(job.error || 'Unknown error')}">Retry</button>`;
    }

    return `<button class="action-btn" data-action="resolve" data-id="${a.id}">${a.resolved ? 'Unresolve' : 'Resolve'}</button>`;
  },

  _escapeHtml(str) {
    if (!str) return '';
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  },

  _onItemClick(id) {
    const ann = this.annotations.find(a => a.id === id);
    if (!ann) return;

    // Seek to timestamp
    if (ann.video) {
      const currentSectionId = VideoPlayer.getCurrentSectionId();
      const isFullMode = VideoPlayer.getSourceType() === 'full';

      if (ann.video.source === 'section' && ann.video.sectionId) {
        if (isFullMode || currentSectionId !== ann.video.sectionId) {
          VideoPlayer.switchToSection(ann.video.sectionId);
        }
      }

      setTimeout(() => {
        VideoPlayer.seekTo(ann.video.timestamp);
      }, 200);
    }

    // Load drawing
    if (ann.drawing) {
      CanvasOverlay.loadDrawingData(ann.drawing);
    } else {
      CanvasOverlay.clear();
    }

    // Enter edit mode
    this._enterEditMode(ann);
  },

  _enterEditMode(ann) {
    this.editingId = ann.id;
    this.currentAnalysis = ann.analysis;

    document.querySelector('.new-annotation h3').textContent = 'Edit Annotation';
    document.getElementById('annotation-text').value = ann.text ? ann.text.content : '';
    document.getElementById('save-btn').textContent = 'Save Changes';
    document.getElementById('analyze-btn').textContent = 'Re-analyze with Claude';
    document.getElementById('cancel-edit-btn').style.display = '';

    if (ann.analysis && ann.analysis.status === 'completed') {
      this._renderEditableAnalysis(ann.analysis);
    } else if (ann.analysis && ann.analysis.status === 'analyzing') {
      const el = document.getElementById('analysis-result');
      el.style.display = 'block';
      el.innerHTML = '<div class="loading">Analysis in progress...</div>';
    } else {
      document.getElementById('analysis-result').style.display = 'none';
    }

    this.renderList();
  },

  exitEditMode() {
    this.editingId = null;
    this.currentAnalysis = null;

    document.querySelector('.new-annotation h3').textContent = 'New Annotation';
    document.getElementById('annotation-text').value = '';
    document.getElementById('save-btn').textContent = 'Save';
    document.getElementById('analyze-btn').textContent = 'Analyze with Claude';
    document.getElementById('cancel-edit-btn').style.display = 'none';
    document.getElementById('analysis-result').style.display = 'none';

    CanvasOverlay.clear();
    SpeechInput.wasUsed = false;
    this.renderList();
  },

  async analyze() {
    const text = document.getElementById('annotation-text').value.trim();
    if (!text) return;

    const btn = document.getElementById('analyze-btn');
    const resultEl = document.getElementById('analysis-result');

    btn.disabled = true;
    btn.textContent = 'Analyzing...';
    resultEl.style.display = 'block';
    resultEl.innerHTML = '<div class="loading">Analyzing with Claude...</div>';

    try {
      const sectionId = VideoPlayer.getCurrentSectionId();
      const timestamp = VideoPlayer.getFormattedTime();
      const analysis = await ApiClient.analyze(text, sectionId, timestamp);

      if (analysis.status === 'error') {
        resultEl.innerHTML = `<div class="error">Error: ${this._escapeHtml(analysis.error)}</div>`;
      } else if (analysis.raw) {
        this.currentAnalysis = analysis;
        resultEl.innerHTML = `<div class="field"><div class="field-value">${this._escapeHtml(analysis.summary)}</div></div>`;
      } else {
        this.currentAnalysis = analysis;
        this._renderAnalysis(analysis);
      }
    } catch (err) {
      resultEl.innerHTML = `<div class="error">Error: ${this._escapeHtml(err.message)}</div>`;
    }

    btn.disabled = false;
    btn.textContent = 'Analyze with Claude';
  },

  async _reanalyze() {
    if (!this.editingId) return;

    const text = document.getElementById('annotation-text').value.trim();
    if (!text) return;

    // Save current text first so server analyzes latest version
    await ApiClient.updateAnnotation(this.editingId, { text: { content: text, inputMethod: 'typed' } });

    const btn = document.getElementById('analyze-btn');
    const resultEl = document.getElementById('analysis-result');
    btn.disabled = true;
    btn.textContent = 'Analyzing...';
    resultEl.style.display = 'block';
    resultEl.innerHTML = '<div class="loading">Re-analyzing with Claude...</div>';

    try {
      const updated = await ApiClient.analyzeAnnotation(this.editingId);
      const idx = this.annotations.findIndex(a => a.id === this.editingId);
      if (idx !== -1) this.annotations[idx] = updated;

      this.currentAnalysis = updated.analysis;
      this._renderEditableAnalysis(updated.analysis);
      this.renderList();
    } catch (err) {
      resultEl.innerHTML = `<div class="error">Error: ${this._escapeHtml(err.message)}</div>`;
    }

    btn.disabled = false;
    btn.textContent = 'Re-analyze with Claude';
  },

  _renderAnalysis(analysis) {
    const el = document.getElementById('analysis-result');
    el.style.display = 'block';

    const fixes = analysis.suggestedFixes
      ? '<ul>' + analysis.suggestedFixes.map(f => `<li>${this._escapeHtml(f)}</li>`).join('') + '</ul>'
      : '';

    const files = analysis.relevantFiles
      ? analysis.relevantFiles.map(f => this._escapeHtml(f)).join(', ')
      : '';

    el.innerHTML = `
      <h4>Claude Analysis</h4>
      <div class="field">
        <div class="field-label">Severity</div>
        <div class="field-value"><span class="severity-badge ${analysis.severity || ''}">${analysis.severity || 'unknown'}</span></div>
      </div>
      <div class="field">
        <div class="field-label">Category</div>
        <div class="field-value">${this._escapeHtml(analysis.category || '')}</div>
      </div>
      <div class="field">
        <div class="field-label">Summary</div>
        <div class="field-value">${this._escapeHtml(analysis.summary || '')}</div>
      </div>
      <div class="field">
        <div class="field-label">Technical Assessment</div>
        <div class="field-value">${this._escapeHtml(analysis.technicalAssessment || '')}</div>
      </div>
      ${fixes ? `<div class="field"><div class="field-label">Suggested Fixes</div>${fixes}</div>` : ''}
      ${files ? `<div class="field"><div class="field-label">Relevant Files</div><div class="field-value">${files}</div></div>` : ''}
      ${analysis.specReference ? `<div class="field"><div class="field-label">Spec Reference</div><div class="field-value">${this._escapeHtml(analysis.specReference)}</div></div>` : ''}
    `;
  },

  _renderEditableAnalysis(analysis) {
    const el = document.getElementById('analysis-result');
    el.style.display = 'block';

    if (!analysis || analysis.status === 'pending') {
      el.innerHTML = '<div class="loading">Analysis pending...</div>';
      return;
    }

    const severityOptions = ['critical', 'high', 'medium', 'low', 'informational']
      .map(s => `<option value="${s}" ${analysis.severity === s ? 'selected' : ''}>${s}</option>`)
      .join('');

    const fixes = analysis.suggestedFixes ? analysis.suggestedFixes.join('\n') : '';

    const files = analysis.relevantFiles
      ? analysis.relevantFiles.map(f => this._escapeHtml(f)).join(', ')
      : '';

    el.innerHTML = `
      <h4>Claude Analysis</h4>
      <div class="field">
        <div class="field-label">Severity</div>
        <div class="field-value"><select id="edit-severity" class="edit-field">${severityOptions}</select></div>
      </div>
      <div class="field">
        <div class="field-label">Category</div>
        <div class="field-value"><input id="edit-category" class="edit-field" type="text" value="${this._escapeHtml(analysis.category || '')}"></div>
      </div>
      <div class="field">
        <div class="field-label">Summary</div>
        <div class="field-value"><textarea id="edit-summary" class="edit-field" rows="2">${this._escapeHtml(analysis.summary || '')}</textarea></div>
      </div>
      <div class="field">
        <div class="field-label">Technical Assessment</div>
        <div class="field-value"><textarea id="edit-assessment" class="edit-field" rows="3">${this._escapeHtml(analysis.technicalAssessment || '')}</textarea></div>
      </div>
      <div class="field">
        <div class="field-label">Suggested Fixes (one per line)</div>
        <div class="field-value"><textarea id="edit-fixes" class="edit-field" rows="3">${this._escapeHtml(fixes)}</textarea></div>
      </div>
      ${files ? `<div class="field"><div class="field-label">Relevant Files</div><div class="field-value">${files}</div></div>` : ''}
      ${analysis.specReference ? `<div class="field"><div class="field-label">Spec Reference</div><div class="field-value">${this._escapeHtml(analysis.specReference)}</div></div>` : ''}
    `;
  },

  _getEditedAnalysis() {
    const severityEl = document.getElementById('edit-severity');
    if (!severityEl) return this.currentAnalysis;

    return {
      ...this.currentAnalysis,
      severity: severityEl.value,
      category: document.getElementById('edit-category').value,
      summary: document.getElementById('edit-summary').value,
      technicalAssessment: document.getElementById('edit-assessment').value,
      suggestedFixes: document.getElementById('edit-fixes').value.split('\n').filter(s => s.trim()),
      status: 'completed',
    };
  },

  async _runBackgroundAnalysis(id) {
    const ann = this.annotations.find(a => a.id === id);
    if (ann) {
      ann.analysis = { status: 'analyzing' };
      this.renderList();
    }

    try {
      const updated = await ApiClient.analyzeAnnotation(id);
      const idx = this.annotations.findIndex(a => a.id === id);
      if (idx !== -1) {
        this.annotations[idx] = updated;
        this.renderList();
      }
    } catch (err) {
      console.error('Background analysis failed:', err);
      const a = this.annotations.find(a => a.id === id);
      if (a) {
        a.analysis = { status: 'error', error: err.message };
        this.renderList();
      }
    }
  },

  async save() {
    const textEl = document.getElementById('annotation-text');
    const text = textEl.value.trim();
    if (!text) return;

    // Edit mode: update existing annotation
    if (this.editingId) {
      const analysis = this._getEditedAnalysis();
      const updates = {
        text: { content: text, inputMethod: 'typed' },
      };
      if (analysis) updates.analysis = analysis;
      const updated = await ApiClient.updateAnnotation(this.editingId, updates);
      const idx = this.annotations.findIndex(a => a.id === this.editingId);
      if (idx !== -1) this.annotations[idx] = { ...this.annotations[idx], ...updated };
      this.exitEditMode();
      return;
    }

    // New annotation
    const frameThumbnailDataUrl = VideoPlayer.captureFrame();
    let frameThumbnail = frameThumbnailDataUrl;
    if (frameThumbnailDataUrl && frameThumbnailDataUrl.startsWith('data:')) {
      const result = await ApiClient.uploadThumbnail(frameThumbnailDataUrl);
      frameThumbnail = result.url;
    }

    const video = {
      source: VideoPlayer.getSourceType(),
      sectionId: VideoPlayer.getCurrentSectionId(),
      file: VideoPlayer.getCurrentFile(),
      timestamp: VideoPlayer.getCurrentTime(),
      timestampFormatted: VideoPlayer.getFormattedTime(),
      frameThumbnail,
    };

    const drawing = CanvasOverlay.hasDrawing() ? CanvasOverlay.getDrawingData() : null;
    if (drawing) {
      const compositeDataUrl = CanvasOverlay.compositeWithVideo(VideoPlayer.video);
      if (compositeDataUrl && compositeDataUrl.startsWith('data:')) {
        const result = await ApiClient.uploadThumbnail(compositeDataUrl);
        drawing.compositeImage = result.url;
      } else {
        drawing.compositeImage = compositeDataUrl;
      }
    }

    const annotation = {
      video,
      text: {
        content: text,
        inputMethod: SpeechInput.wasUsed ? 'mixed' : 'typed',
      },
      drawing,
      analysis: this.currentAnalysis ? { ...this.currentAnalysis, status: 'completed' } : { status: 'pending' },
      tags: [],
      resolved: false,
    };

    const saved = await ApiClient.createAnnotation(annotation);
    this.annotations.push(saved);
    this.renderList();

    // Trigger background analysis if none exists yet
    if (!this.currentAnalysis) {
      this._runBackgroundAnalysis(saved.id);
    }

    // Reset form
    textEl.value = '';
    this.currentAnalysis = null;
    document.getElementById('analysis-result').style.display = 'none';
    CanvasOverlay.clear();
    SpeechInput.wasUsed = false;

    // Scroll to bottom of list
    this.listEl.scrollTop = this.listEl.scrollHeight;
  },

  async _toggleResolved(id) {
    const ann = this.annotations.find(a => a.id === id);
    if (!ann) return;

    // If already resolved, just unresolve (toggle back)
    if (ann.resolved === true) {
      ann.resolved = false;
      ann.resolveJob = null;
      await ApiClient.updateAnnotation(id, { resolved: false, resolveJob: null });
      this.renderList();
      return;
    }

    // If job is already pending or running, ignore
    if (ann.resolveJob && (ann.resolveJob.status === 'pending' || ann.resolveJob.status === 'running')) {
      return;
    }

    // Require completed analysis
    if (!ann.analysis || ann.analysis.status !== 'completed') {
      alert('Please run analysis first before resolving.');
      return;
    }

    // Start resolve pipeline
    try {
      const { jobId } = await ApiClient.resolveAnnotation(id);
      ann.resolveJob = { jobId, status: 'pending' };
      this.renderList();

      this._streamResolveJob(id, jobId);
    } catch (err) {
      console.error('Resolve failed:', err);
      ann.resolveJob = { status: 'error', error: err.message };
      this.renderList();
    }
  },

  _streamResolveJob(annotationId, jobId) {
    ApiClient.streamJob(
      jobId,
      // onUpdate
      (data) => {
        const ann = this.annotations.find(a => a.id === annotationId);
        if (!ann) return;
        ann.resolveJob = { jobId, ...data };
        this.renderList();
      },
      // onDone
      (data) => {
        const ann = this.annotations.find(a => a.id === annotationId);
        if (ann) {
          ann.resolved = true;
          ann.resolveJob = { jobId, status: 'done' };
          this.renderList();
        }
        this._reloadVideo();
      },
      // onError
      (errMsg) => {
        const ann = this.annotations.find(a => a.id === annotationId);
        if (ann) {
          ann.resolveJob = { jobId, status: 'error', error: errMsg };
          this.renderList();
        }
      }
    );
  },

  _reloadVideo() {
    if (typeof VideoPlayer !== 'undefined' && VideoPlayer.switchToSection) {
      const currentId = VideoPlayer.getCurrentSectionId ? VideoPlayer.getCurrentSectionId() : null;
      VideoPlayer.switchToSection(currentId);
    }
  },

  async _delete(id) {
    if (this.editingId === id) this.exitEditMode();
    await ApiClient.deleteAnnotation(id);
    this.annotations = this.annotations.filter(a => a.id !== id);
    this.renderList();
  },
};
