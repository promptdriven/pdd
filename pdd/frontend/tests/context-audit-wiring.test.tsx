import React from 'react';
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen } from '@testing-library/react';

import { api, ContextAuditResponse } from '../api';
import PromptMetricsBar from '../components/PromptMetricsBar';

// PR #1387 review item 1+2: `pdd connect`'s prompt screen must call
// api.contextAudit(...) in the same debounced flow as analyzePrompt — passing
// the current editor content so the per-source breakdown reflects unsaved edits
// — and PromptMetricsBar must render that breakdown. These contract tests guard
// both halves of the wiring (a full PromptSpace render is impractical here, so
// we pin the API client and the consuming component instead).

describe('api.contextAudit (client contract)', () => {
  beforeEach(() => {
    vi.restoreAllMocks();
  });
  afterEach(() => {
    vi.restoreAllMocks();
  });

  it('POSTs path, model, and override content to the context-audit endpoint', async () => {
    const payload: ContextAuditResponse = {
      total_tokens: 42,
      context_limit: 1000,
      percent_used: 4.2,
      model: 'gpt-4o',
      rows: [],
      warnings: [],
      threshold_exceeded: false,
    };
    const fetchMock = vi.fn().mockResolvedValue({
      ok: true,
      json: async () => payload,
    });
    vi.stubGlobal('fetch', fetchMock);

    const result = await api.contextAudit({
      path: 'prompts/calc_python.prompt',
      model: 'gpt-4o',
      content: 'unsaved editor body',
    });

    expect(result).toEqual(payload);
    expect(fetchMock).toHaveBeenCalledTimes(1);
    const [url, options] = fetchMock.mock.calls[0];
    expect(url).toContain('/api/v1/prompts/context-audit');
    expect(options.method).toBe('POST');
    // The unsaved editor content must be forwarded so the audit reflects it.
    const body = JSON.parse(options.body);
    expect(body).toMatchObject({
      path: 'prompts/calc_python.prompt',
      model: 'gpt-4o',
      content: 'unsaved editor body',
    });
  });
});

describe('PromptMetricsBar (renders the context audit breakdown)', () => {
  const baseProps = {
    rawMetrics: null,
    processedMetrics: null,
    viewMode: 'raw' as const,
    onViewModeChange: () => {},
    isLoading: false,
  };

  it('shows the per-source breakdown when a contextAudit prop is provided', () => {
    const contextAudit: ContextAuditResponse = {
      total_tokens: 100,
      context_limit: 1000,
      percent_used: 10,
      model: 'gpt-4o',
      rows: [
        { source: 'context/a.txt', tokens: 80, percent: 80, status: 'resolved', note: null },
        { source: 'prompt_body', tokens: 20, percent: 20, status: 'body', note: null },
      ],
      warnings: [],
      threshold_exceeded: false,
    };

    render(<PromptMetricsBar {...baseProps} contextAudit={contextAudit} />);

    expect(screen.getByText('Context usage by source')).toBeInTheDocument();
    expect(screen.getByText('context/a.txt')).toBeInTheDocument();
    expect(screen.getByText('prompt_body')).toBeInTheDocument();
  });

  it('renders nothing extra when no contextAudit is provided', () => {
    render(<PromptMetricsBar {...baseProps} contextAudit={null} />);
    expect(screen.queryByText('Context usage by source')).not.toBeInTheDocument();
  });
});
