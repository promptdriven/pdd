import { describe, it, expect, jest, beforeEach } from '@jest/globals';

// Mock child_process before importing
jest.mock('child_process', () => ({
  execSync: jest.fn(),
}));

import { execSync } from 'child_process';
import { isGitAvailable, preFixCommit, fixCommit, getFixDiff, revertFix } from '../lib/git';

const mockExecSync = execSync as jest.MockedFunction<typeof execSync>;

describe('lib/git', () => {
  beforeEach(() => {
    jest.clearAllMocks();
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
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))   // isGitAvailable
        .mockReturnValueOnce(Buffer.from(''))        // git add
        .mockReturnValueOnce(Buffer.from('file.tsx')) // git diff --cached
        .mockReturnValueOnce(Buffer.from(''))        // git commit
        .mockReturnValueOnce(Buffer.from('abc123\n')); // git rev-parse
      expect(preFixCommit('s1', 'b1')).toBe('abc123');
    });

    it('returns null when nothing to commit', () => {
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))   // isGitAvailable
        .mockReturnValueOnce(Buffer.from(''))        // git add
        .mockReturnValueOnce(Buffer.from(''));        // git diff --cached (empty)
      expect(preFixCommit('s1', 'b1')).toBeNull();
    });

    it('returns null when git is not available', () => {
      mockExecSync.mockImplementation(() => { throw new Error('not a git repo'); });
      expect(preFixCommit('s1', 'b1')).toBeNull();
    });
  });

  describe('fixCommit', () => {
    it('creates a fix commit and returns SHA', () => {
      mockExecSync
        .mockReturnValueOnce(Buffer.from('true'))     // isGitAvailable
        .mockReturnValueOnce(Buffer.from(''))          // git add
        .mockReturnValueOnce(Buffer.from('file.tsx'))  // git diff --cached
        .mockReturnValueOnce(Buffer.from(''))          // git commit
        .mockReturnValueOnce(Buffer.from('def456\n')); // git rev-parse
      expect(fixCommit('ann-1', 'Fix text alignment')).toBe('def456');
    });

    it('sanitizes summary in commit message', () => {
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
