import { describe, it, expect } from 'vitest';
import { moduleNeedsSync } from '../components/ArchitectureView';
import type { PromptInfo } from '../api';

describe('moduleNeedsSync', () => {
  it('returns true when info is undefined', () => {
    expect(moduleNeedsSync(undefined)).toBe(true);
  });

  it('returns true when code is missing (default outputs)', () => {
    const info: PromptInfo = {
      prompt: 'prompts/calc_python.prompt',
      sync_basename: 'calc',
      language: 'python',
      test: 'tests/test_calc.py',
      example: 'examples/calc_example.py',
    };
    expect(moduleNeedsSync(info)).toBe(true);
  });

  it('returns true when test is missing (default outputs)', () => {
    const info: PromptInfo = {
      prompt: 'prompts/calc_python.prompt',
      sync_basename: 'calc',
      language: 'python',
      code: 'src/calc.py',
      example: 'examples/calc_example.py',
    };
    expect(moduleNeedsSync(info)).toBe(true);
  });

  it('returns true when example is missing (default outputs)', () => {
    const info: PromptInfo = {
      prompt: 'prompts/calc_python.prompt',
      sync_basename: 'calc',
      language: 'python',
      code: 'src/calc.py',
      test: 'tests/test_calc.py',
    };
    expect(moduleNeedsSync(info)).toBe(true);
  });

  it('returns false when all default outputs present', () => {
    const info: PromptInfo = {
      prompt: 'prompts/calc_python.prompt',
      sync_basename: 'calc',
      language: 'python',
      code: 'src/calc.py',
      test: 'tests/test_calc.py',
      example: 'examples/calc_example.py',
    };
    expect(moduleNeedsSync(info)).toBe(false);
  });

  it('returns false for code-only language when code exists', () => {
    const info: PromptInfo = {
      prompt: 'prompts/package_json.prompt',
      sync_basename: 'package',
      language: 'json',
      expected_outputs: ['code'],
      code: 'package.json',
    };
    expect(moduleNeedsSync(info)).toBe(false);
  });

  it('returns true for code-only language when code is missing', () => {
    const info: PromptInfo = {
      prompt: 'prompts/tsconfig_json.prompt',
      sync_basename: 'tsconfig',
      language: 'json',
      expected_outputs: ['code'],
    };
    expect(moduleNeedsSync(info)).toBe(true);
  });

  it('falls back to requiring all three when expected_outputs is undefined', () => {
    // No expected_outputs → defaults to ['code', 'test', 'example']
    const info: PromptInfo = {
      prompt: 'prompts/calc_python.prompt',
      sync_basename: 'calc',
      language: 'python',
      code: 'src/calc.py',
      // test and example missing → needs sync
    };
    expect(moduleNeedsSync(info)).toBe(true);
  });
});
