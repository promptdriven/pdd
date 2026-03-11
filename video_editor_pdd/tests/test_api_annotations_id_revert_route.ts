import { describe, it, expect, jest, beforeEach } from '@jest/globals';
import fsPromises from 'fs/promises';

jest.mock('../lib/db', () => ({
  getDb: jest.fn(),
}));
jest.mock('../lib/git', () => ({
  revertFix: jest.fn(),
}));
jest.mock('../lib/render', () => ({
  renderSection: jest.fn(),
  stitchFullVideo: jest.fn(),
}));
jest.mock('../lib/project', () => ({
  loadProject: jest.fn(),
  getSection: jest.fn(),
}));
jest.mock('../lib/jobs', () => ({
  runPipelineStage: jest.fn(),
}));
jest.mock('child_process', () => ({
  execSync: jest.fn(),
}));

import { getDb } from '../lib/db';
import { revertFix } from '../lib/git';
import { renderSection, stitchFullVideo } from '../lib/render';
import { loadProject, getSection } from '../lib/project';
import { runPipelineStage } from '../lib/jobs';
import { POST } from '../app/api/annotations/[id]/revert/route';

const mockGetDb = getDb as jest.MockedFunction<typeof getDb>;
const mockRevertFix = revertFix as jest.MockedFunction<typeof revertFix>;
const mockRenderSection = renderSection as jest.MockedFunction<typeof renderSection>;
const mockStitchFullVideo = stitchFullVideo as jest.MockedFunction<typeof stitchFullVideo>;
const mockLoadProject = loadProject as jest.MockedFunction<typeof loadProject>;
const mockGetSection = getSection as jest.MockedFunction<typeof getSection>;
const mockRunPipelineStage = runPipelineStage as jest.MockedFunction<typeof runPipelineStage>;

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
    mockRenderSection.mockResolvedValue(undefined);
    mockStitchFullVideo.mockResolvedValue(undefined);
    mockRunPipelineStage.mockResolvedValue('job-veo-001');
    mockLoadProject.mockReturnValue({
      sections: [
        { id: 's1', compositionId: 'SectionOne', durationSeconds: 10, offsetSeconds: 0 },
        { id: 's2', compositionId: 'SectionTwo', durationSeconds: 10, offsetSeconds: 10 },
      ],
    } as any);
    mockGetSection.mockReturnValue({
      id: 's1',
      compositionId: 'SectionOne',
      durationSeconds: 10,
      offsetSeconds: 0,
    } as any);
    jest.spyOn(fsPromises, 'rm').mockResolvedValue(undefined);
    jest.spyOn(fsPromises, 'readdir').mockResolvedValue([] as any);
    jest.spyOn(fsPromises, 'mkdir').mockResolvedValue(undefined);
    jest.spyOn(fsPromises, 'copyFile').mockResolvedValue(undefined);
    jest.spyOn(fsPromises, 'access').mockResolvedValue(undefined);
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

  it('reverts commit, rerenders the section, and clears annotation', async () => {
    mockDb.prepare().get.mockReturnValue({
      fixCommitSha: 'abc123',
      sectionId: 's1',
      analysis: JSON.stringify({ fixType: 'remotion' }),
    });
    mockRevertFix.mockReturnValue('rev789');
    const res = await POST(makeRequest(), { params: { id: 'ann-1' } });
    expect(res.status).toBe(200);
    const body = await res.json();
    expect(body.revertCommitSha).toBe('rev789');
    expect(body.sectionId).toBe('s1');
    expect(mockRun).toHaveBeenCalled();
    expect(mockRenderSection).toHaveBeenCalledWith(
      'SectionOne',
      'outputs/sections/s1.mp4',
      expect.any(Function)
    );
    expect(mockStitchFullVideo).toHaveBeenCalled();
  });

  it('reruns veo generation before rerendering when undoing a veo fix', async () => {
    mockDb.prepare().get.mockReturnValue({
      fixCommitSha: 'abc123',
      sectionId: 's1',
      analysis: JSON.stringify({ fixType: 'veo' }),
    });
    mockRevertFix.mockReturnValue('rev789');

    const res = await POST(makeRequest(), { params: { id: 'ann-1' } });

    expect(res.status).toBe(200);
    expect(mockRunPipelineStage).toHaveBeenCalledWith(
      'veo',
      { clips: ['s1'] },
      expect.any(Function)
    );
  });
});
