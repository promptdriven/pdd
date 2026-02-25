import { describe, it, expect, jest, beforeEach } from '@jest/globals';

jest.mock('../lib/db', () => ({
  getDb: jest.fn(),
}));
jest.mock('../lib/claude', () => ({
  runClaudeFixDryRun: jest.fn(),
}));
jest.mock('../lib/jobs', () => ({
  createJob: jest.fn(),
  runJob: jest.fn(),
}));
jest.mock('../lib/sse', () => ({
  createSseStream: jest.fn(),
}));

import { getDb } from '../lib/db';
import { runClaudeFixDryRun } from '../lib/claude';
import { POST } from '../app/api/sections/[id]/preview-fixes/route';

const mockGetDb = getDb as jest.MockedFunction<typeof getDb>;
const mockDryRun = runClaudeFixDryRun as jest.MockedFunction<typeof runClaudeFixDryRun>;

function makeRequest(body?: object) {
  return new Request('http://localhost:3000/api/sections/s1/preview-fixes', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: body ? JSON.stringify(body) : undefined,
  });
}

describe('POST /api/sections/[id]/preview-fixes', () => {
  let mockDb: any;

  beforeEach(() => {
    jest.clearAllMocks();
    mockDb = {
      prepare: jest.fn().mockReturnValue({
        all: jest.fn().mockReturnValue([]),
        get: jest.fn(),
        run: jest.fn(),
      }),
    };
    mockGetDb.mockReturnValue(mockDb);
  });

  it('returns empty previews when no unresolved annotations', async () => {
    mockDb.prepare().all.mockReturnValue([]);
    const res = await POST(makeRequest(), { params: { id: 's1' } });
    expect(res.status).toBe(200);
    const body = await res.json();
    expect(body.previews).toEqual([]);
  });

  it('generates preview for remotion annotation', async () => {
    mockDb.prepare().all.mockReturnValue([
      {
        id: 'ann-1',
        sectionId: 's1',
        timestamp: 10.0,
        text: 'Fix the text alignment',
        videoFile: null,
        drawingDataUrl: null,
        compositeDataUrl: null,
        analysis: JSON.stringify({
          severity: 'major',
          fixType: 'remotion',
          technicalAssessment: 'Text is misaligned',
          suggestedFixes: ['Adjust position'],
          confidence: 0.85,
        }),
        resolved: 0,
        resolveJobId: null,
        createdAt: '2026-01-01',
      },
    ]);

    mockDryRun.mockResolvedValue({
      fixType: 'remotion',
      filesModified: ['Section1.tsx'],
      changeDescription: 'Adjust text position from left to center',
      confidence: 0.9,
      proposedDiff: '--- a/Section1.tsx\n+++ b/Section1.tsx\n-left\n+center',
    });

    const res = await POST(makeRequest(), { params: { id: 's1' } });
    expect(res.status).toBe(200);
    const body = await res.json();
    expect(body.previews).toHaveLength(1);
    expect(body.previews[0].fixType).toBe('remotion');
    expect(body.previews[0].diff).toContain('center');
  });

  it('generates placeholder for veo annotation', async () => {
    mockDb.prepare().all.mockReturnValue([
      {
        id: 'ann-2',
        sectionId: 's1',
        timestamp: 5.0,
        text: 'Wrong clip',
        videoFile: null,
        drawingDataUrl: null,
        compositeDataUrl: null,
        analysis: JSON.stringify({
          severity: 'major',
          fixType: 'veo',
          technicalAssessment: 'Clip doesnt match',
          suggestedFixes: ['Regenerate'],
          confidence: 0.7,
        }),
        resolved: 0,
        resolveJobId: null,
        createdAt: '2026-01-01',
      },
    ]);

    const res = await POST(makeRequest(), { params: { id: 's1' } });
    const body = await res.json();
    expect(body.previews[0].fixType).toBe('veo');
    expect(body.previews[0].preview).toContain('Veo clip');
  });

  it('filters by annotationIds when provided', async () => {
    mockDb.prepare().all.mockReturnValue([]);
    await POST(makeRequest({ annotationIds: ['ann-1', 'ann-2'] }), { params: { id: 's1' } });
    // Verify prepare was called with the filtered query
    const prepareCall = mockDb.prepare.mock.calls.find(
      (call: string[]) => typeof call[0] === 'string' && call[0].includes('IN')
    );
    expect(prepareCall).toBeDefined();
  });
});
