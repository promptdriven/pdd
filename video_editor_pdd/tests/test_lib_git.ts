import { describe, it, expect, jest, beforeEach } from '@jest/globals';
import fs from 'fs';
import os from 'os';
import path from 'path';

// Mock child_process before importing
jest.mock('child_process', () => ({
  execSync: jest.fn(),
}));

import { execSync } from 'child_process';
import {
  isGitAvailable,
  preFixCommit,
  preFixCommitWithPaths,
  fixCommit,
  getFixDiff,
  revertFix,
} from '../lib/git';

const mockExecSync = execSync as jest.MockedFunction<typeof execSync>;

describe('lib/git', () => {
  beforeEach(() => {
    mockExecSync.mockReset();
  });

  describe('isGitAvailable', () => {
    it('returns true when git is available', () => {
      mockExecSync.mockReturnValue(Buffer.from('true'));
      expect(isGitAvailable()).toBe(true);
    });

    it('returns false when git is not available', () => {
      mockExecSync.mockImplementation(() => { throw new Error('not a git repo'); });
      expect(isGitAvailable()).toBe(false);
    });
  });

  describe('preFixCommit', () => {
    it('creates a commit and returns SHA', () => {
      const existsSpy = jest.spyOn(fs, 'existsSync').mockReturnValue(true);
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))   // isGitAvailable
        .mockReturnValueOnce(Buffer.from(''))        // git add
        .mockReturnValueOnce(Buffer.from('file.tsx')) // git diff --cached
        .mockReturnValueOnce(Buffer.from(''))        // git commit
        .mockReturnValueOnce(Buffer.from('abc123\n')); // git rev-parse
      expect(preFixCommit('s1', 'b1')).toBe('abc123');
      existsSpy.mockRestore();
    });

    it('returns null when nothing to commit', () => {
      const existsSpy = jest.spyOn(fs, 'existsSync').mockReturnValue(true);
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))   // isGitAvailable
        .mockReturnValueOnce(Buffer.from(''))        // git add
        .mockReturnValueOnce(Buffer.from(''));        // git diff --cached (empty)
      expect(preFixCommit('s1', 'b1')).toBeNull();
      existsSpy.mockRestore();
    });

    it('returns null when git is not available', () => {
      mockExecSync.mockImplementation(() => { throw new Error('not a git repo'); });
      expect(preFixCommit('s1', 'b1')).toBeNull();
    });

    it('stages custom absolute paths when provided', () => {
      const projectDir = path.join(process.cwd(), 'projects', 'demo');
      const remotionDir = path.join(projectDir, 'remotion', 'src', 'remotion');
      const specsDir = path.join(projectDir, 'specs');
      const existsSpy = jest.spyOn(fs, 'existsSync').mockImplementation((candidate) =>
        candidate === remotionDir || candidate === specsDir
      );

      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('specs/veo_section/veo.json'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('sha\n'));

      expect(preFixCommitWithPaths('s1', 'b1', [remotionDir, specsDir])).toBe('sha');

      const addCall = mockExecSync.mock.calls.find(
        (call) => typeof call[0] === 'string' && call[0].startsWith('git add')
      );
      expect(addCall).toBeDefined();
      expect(addCall![0]).toContain(remotionDir);
      expect(addCall![0]).toContain(specsDir);
      existsSpy.mockRestore();
    });

    it('ignores missing paths when creating a pre-fix commit', () => {
      const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'git-path-filter-'));
      const remotionDir = path.join(tmpDir, 'remotion', 'src', 'remotion');
      fs.mkdirSync(remotionDir, { recursive: true });
      const missingSpecsDir = path.join(tmpDir, 'specs');
      const existsSpy = jest.spyOn(fs, 'existsSync').mockImplementation((candidate) =>
        candidate === remotionDir
      );

      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('remotion/src/remotion/index.tsx'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('sha\n'));

      expect(preFixCommitWithPaths('s1', 'b1', [remotionDir, missingSpecsDir])).toBe('sha');

      const addCall = mockExecSync.mock.calls.find(
        (call) => typeof call[0] === 'string' && call[0].startsWith('git add')
      );
      expect(addCall).toBeDefined();
      expect(addCall![0]).toContain(remotionDir);
      expect(addCall![0]).not.toContain(missingSpecsDir);

      existsSpy.mockRestore();
      fs.rmSync(tmpDir, { recursive: true, force: true });
    });
  });

  describe('fixCommit', () => {
    it('creates a fix commit and returns SHA', () => {
      const existsSpy = jest.spyOn(fs, 'existsSync').mockReturnValue(true);
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))     // isGitAvailable
        .mockReturnValueOnce(Buffer.from(''))          // git add
        .mockReturnValueOnce(Buffer.from('file.tsx'))  // git diff --cached
        .mockReturnValueOnce(Buffer.from(''))          // git commit
        .mockReturnValueOnce(Buffer.from('def456\n')); // git rev-parse
      expect(fixCommit('ann-1', 'Fix text alignment')).toBe('def456');
      existsSpy.mockRestore();
    });

    it('stages custom file paths when provided', () => {
      const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'git-fix-filter-'));
      const existingSpecPath = path.join(tmpDir, 'specs', 'veo_section', '02_ocean_wave_sunset.md');
      fs.mkdirSync(path.dirname(existingSpecPath), { recursive: true });
      fs.writeFileSync(existingSpecPath, '# spec\n');
      const existsSpy = jest.spyOn(fs, 'existsSync').mockImplementation((candidate) =>
        candidate === existingSpecPath
      );

      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('specs/veo_section/02_ocean_wave_sunset.md'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('sha\n'));

      fixCommit('ann-1', 'Update Veo prompt', [existingSpecPath, path.join(tmpDir, 'missing.md')]);

      const addCall = mockExecSync.mock.calls.find(
        (call) => typeof call[0] === 'string' && call[0].startsWith('git add')
      );
      expect(addCall).toBeDefined();
      expect(addCall![0]).toContain(existingSpecPath);
      expect(addCall![0]).not.toContain(path.join(tmpDir, 'missing.md'));

      existsSpy.mockRestore();
      fs.rmSync(tmpDir, { recursive: true, force: true });
    });

    it('sanitizes summary in commit message', () => {
      const existsSpy = jest.spyOn(fs, 'existsSync').mockReturnValue(true);
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('file.tsx'))
        .mockReturnValueOnce(Buffer.from(''))
        .mockReturnValueOnce(Buffer.from('sha\n'));
      fixCommit('ann-1', 'Fix "bad" stuff\nwith newlines');
      // Verify commit message was sanitized (no quotes or newlines)
      const commitCall = mockExecSync.mock.calls.find(
        (call) => typeof call[0] === 'string' && call[0].startsWith('git commit')
      );
      expect(commitCall).toBeDefined();
      expect(commitCall![0]).not.toContain('\n');
      existsSpy.mockRestore();
    });
  });

  describe('getFixDiff', () => {
    it('returns diff text for a commit', () => {
      mockExecSync.mockReturnValue(Buffer.from('diff --git a/file.tsx b/file.tsx\n+added line'));
      const diff = getFixDiff('abc123');
      expect(diff).toContain('diff --git');
    });

    it('throws on invalid commit', () => {
      mockExecSync.mockImplementation(() => { throw new Error('bad object'); });
      expect(() => getFixDiff('invalid')).toThrow('Failed to get diff');
    });
  });

  describe('revertFix', () => {
    it('reverts a commit and returns new SHA', () => {
      mockExecSync
        .mockReturnValueOnce(Buffer.from(''))          // git revert
        .mockReturnValueOnce(Buffer.from('rev789\n')); // git rev-parse
      expect(revertFix('abc123')).toBe('rev789');
    });

    it('throws when revert fails', () => {
      mockExecSync.mockImplementation(() => { throw new Error('conflict'); });
      expect(() => revertFix('abc123')).toThrow('Failed to revert');
    });

    it('includes original git error in revert failure message', () => {
      // Simulate a realistic execSync error with stderr (as Node child_process produces)
      const execError = new Error('Command failed: git revert --no-edit abc123');
      (execError as any).stderr = Buffer.from('error: could not revert abc123... dirty working tree');
      (execError as any).status = 1;
      mockExecSync.mockImplementation(() => { throw execError; });
      expect(() => revertFix('abc123')).toThrow('dirty working tree');
    });
  });
});
