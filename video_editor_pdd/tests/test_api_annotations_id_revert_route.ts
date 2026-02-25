import { describe, it, expect, jest, beforeEach } from '@jest/globals';

jest.mock('../lib/db', () => ({
  getDb: jest.fn(),
}));
jest.mock('../lib/git', () => ({
  revertFix: jest.fn(),
}));

import { getDb } from '../lib/db';
import { revertFix } from '../lib/git';
import { POST } from '../app/api/annotations/[id]/revert/route';

const mockGetDb = getDb as jest.MockedFunction<typeof getDb>;
const mockRevertFix = revertFix as jest.MockedFunction<typeof revertFix>;

function makeRequest() {
  return new Request('http://localhost:3000/api/annotations/ann-1/revert', { method: 'POST' });
}

describe('POST /api/annotations/[id]/revert', () => {
  let mockDb: any;
  let mockRun: jest.Mock;

  beforeEach(() => {
    jest.clearAllMocks();
    mockRun = jest.fn();
    mockDb = {
      prepare: jest.fn().mockReturnValue({
        get: jest.fn(),
        run: mockRun,
      }),
    };
    mockGetDb.mockReturnValue(mockDb);
  });

  it('returns 404 when annotation not found', async () => {
    mockDb.prepare().get.mockReturnValue(undefined);
    const res = await POST(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(404);
  });

  it('returns 404 when no fixCommitSha', async () => {
    mockDb.prepare().get.mockReturnValue({ fixCommitSha: null, sectionId: 's1' });
    const res = await POST(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(404);
  });

  it('reverts commit and clears annotation', async () => {
    mockDb.prepare().get.mockReturnValue({ fixCommitSha: 'abc123', sectionId: 's1' });
    mockRevertFix.mockReturnValue('rev789');
    const res = await POST(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(200);
    const body = await res.json();
    expect(body.revertCommitSha).toBe('rev789');
    expect(body.sectionId).toBe('s1');
    expect(mockRun).toHaveBeenCalled();
  });
});
