/**
 * API client - fetch() wrapper for all backend calls.
 */
const ApiClient = {
  async getSections() {
    const res = await fetch('/api/sections');
    return res.json();
  },

  async getAnnotations() {
    const res = await fetch('/api/annotations');
    return res.json();
  },

  async createAnnotation(annotation) {
    const res = await fetch('/api/annotations', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(annotation),
    });
    return res.json();
  },

  async updateAnnotation(id, updates) {
    const res = await fetch(`/api/annotations/${id}`, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(updates),
    });
    return res.json();
  },

  async deleteAnnotation(id) {
    await fetch(`/api/annotations/${id}`, { method: 'DELETE' });
  },

  async uploadThumbnail(dataUrl) {
    const res = await fetch('/api/thumbnails', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ dataUrl }),
    });
    return res.json();
  },

  async analyzeAnnotation(id) {
    const res = await fetch(`/api/annotations/${id}/analyze`, { method: 'POST' });
    if (!res.ok) {
      const err = await res.json().catch(() => ({}));
      throw new Error(err.error || `Analysis failed (${res.status})`);
    }
    return res.json();
  },

  async analyze(text, sectionId, timestamp) {
    const res = await fetch('/api/analyze', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ text, sectionId, timestamp }),
    });
    return res.json();
  },

  async resolveAnnotation(id) {
    const res = await fetch(`/api/annotations/${id}/resolve`, { method: 'POST' });
    if (!res.ok) {
      const err = await res.json().catch(() => ({}));
      throw new Error(err.error || `Resolve failed (${res.status})`);
    }
    return res.json();
  },

  streamJob(jobId, onUpdate, onDone, onError) {
    const es = new EventSource(`/api/jobs/${jobId}/stream`);
    es.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        onUpdate(data);
        if (data.status === 'done') {
          es.close();
          if (onDone) onDone(data);
        } else if (data.status === 'error') {
          es.close();
          if (onError) onError(data.error);
        }
      } catch (err) {
        console.error('SSE parse error:', err);
      }
    };
    es.onerror = () => {
      es.close();
      // Fallback to polling
      this._pollJob(jobId, onUpdate, onDone, onError);
    };
    return es;
  },

  async _pollJob(jobId, onUpdate, onDone, onError) {
    const poll = async () => {
      try {
        const data = await this.getJob(jobId);
        onUpdate(data);
        if (data.status === 'done') {
          if (onDone) onDone(data);
          return;
        } else if (data.status === 'error') {
          if (onError) onError(data.error);
          return;
        }
        setTimeout(poll, 2000);
      } catch (err) {
        if (onError) onError(err.message);
      }
    };
    poll();
  },

  async getJob(jobId) {
    const res = await fetch(`/api/jobs/${jobId}`);
    if (!res.ok) {
      const err = await res.json().catch(() => ({}));
      throw new Error(err.error || `Job fetch failed (${res.status})`);
    }
    return res.json();
  },

  exportUrl() {
    return '/api/export';
  },
};
