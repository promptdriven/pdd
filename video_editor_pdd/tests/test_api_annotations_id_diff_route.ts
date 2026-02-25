import { describe, it, expect, jest, beforeEach } from '@jest/globals';

jest.mock('../lib/db', () => ({
  getDb: jest.fn(),
}));
jest.mock('../lib/git', () => ({
  getFixDiff: jest.fn(),
}));

import { getDb } from '../lib/db';
import { getFixDiff } from '../lib/git';
import { GET } from '../app/api/annotations/[id]/diff/route';

const mockGetDb = getDb as jest.MockedFunction<typeof getDb>;
const mockGetFixDiff = getFixDiff as jest.MockedFunction<typeof getFixDiff>;

function makeRequest() {
  return new Request('http://localhost:3000/api/annotations/ann-1/diff');
}

describe('GET /api/annotations/[id]/diff', () => {
  let mockDb: any;

  beforeEach(() => {
    jest.clearAllMocks();
    mockDb = {
      prepare: jest.fn().mockReturnValue({
        get: jest.fn(),
      }),
    };
    mockGetDb.mockReturnValue(mockDb);
  });

  it('returns 404 when annotation not found', async () => {
    mockDb.prepare().get.mockReturnValue(undefined);
    const res = await GET(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(404);
  });

  it('returns 404 when no fixCommitSha', async () => {
    mockDb.prepare().get.mockReturnValue({ fixCommitSha: null });
    const res = await GET(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(404);
  });

  it('returns diff when fixCommitSha exists', async () => {
    mockDb.prepare().get.mockReturnValue({ fixCommitSha: 'abc123' });
    mockGetFixDiff.mockReturnValue('diff --git a/file.tsx b/file.tsx\n+line');
    const res = await GET(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(200);
    const body = await res.json();
    expect(body.commitSha).toBe('abc123');
    expect(body.diff).toContain('diff --git');
  });
});
