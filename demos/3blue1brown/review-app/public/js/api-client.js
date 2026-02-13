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

  exportUrl() {
    return '/api/export';
  },
};
