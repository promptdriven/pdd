/**
 * Tests for tsconfig.json
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that tsconfig.json conforms to the specification in
 * prompts/tsconfig_json_json.prompt.
 */

import * as fs from 'fs';
import * as path from 'path';

const TSCONFIG_PATH = path.resolve(__dirname, '..', 'tsconfig.json');

interface TsConfig {
  extends?: string;
  compilerOptions?: Record<string, unknown>;
  include?: string[];
  exclude?: string[];
  [key: string]: unknown;
}

let tsconfig: TsConfig;

beforeAll(() => {
  const raw = fs.readFileSync(TSCONFIG_PATH, 'utf-8');
  tsconfig = JSON.parse(raw) as TsConfig;
});

// ---------------------------------------------------------------------------
// 1. Top-level extends
// ---------------------------------------------------------------------------

describe('tsconfig.json extends', () => {
  it('does not use extends field (config is self-contained)', () => {
    expect(tsconfig.extends).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 2. compilerOptions
// ---------------------------------------------------------------------------

describe('compilerOptions', () => {
  let opts: Record<string, unknown>;

  beforeAll(() => {
    opts = tsconfig.compilerOptions as Record<string, unknown>;
  });

  it('compilerOptions field exists', () => {
    expect(tsconfig.compilerOptions).toBeDefined();
    expect(typeof tsconfig.compilerOptions).toBe('object');
  });

  it('target is "ES2017"', () => {
    expect(opts['target']).toBe('ES2017');
  });

  it('lib is ["dom", "dom.iterable", "esnext"]', () => {
    expect(opts['lib']).toEqual(['dom', 'dom.iterable', 'esnext']);
  });

  it('allowJs is true', () => {
    expect(opts['allowJs']).toBe(true);
  });

  it('skipLibCheck is true', () => {
    expect(opts['skipLibCheck']).toBe(true);
  });

  it('strict is true', () => {
    expect(opts['strict']).toBe(true);
  });

  it('noEmit is true', () => {
    expect(opts['noEmit']).toBe(true);
  });

  it('esModuleInterop is true', () => {
    expect(opts['esModuleInterop']).toBe(true);
  });

  it('module is "esnext"', () => {
    expect(opts['module']).toBe('esnext');
  });

  it('moduleResolution is "bundler"', () => {
    expect(opts['moduleResolution']).toBe('bundler');
  });

  it('resolveJsonModule is true', () => {
    expect(opts['resolveJsonModule']).toBe(true);
  });

  it('isolatedModules is true', () => {
    expect(opts['isolatedModules']).toBe(true);
  });

  it('jsx is "preserve"', () => {
    expect(opts['jsx']).toBe('preserve');
  });

  it('incremental is true', () => {
    expect(opts['incremental']).toBe(true);
  });

  it('paths has "@/*": ["./*"]', () => {
    expect(opts['paths']).toEqual({ '@/*': ['./*'] });
  });

  it('plugins contains { "name": "next" }', () => {
    expect(opts['plugins']).toEqual([{ name: 'next' }]);
  });
});

// ---------------------------------------------------------------------------
// 3. include
// ---------------------------------------------------------------------------

describe('include', () => {
  it('include field exists', () => {
    expect(tsconfig.include).toBeDefined();
    expect(Array.isArray(tsconfig.include)).toBe(true);
  });

  it('include contains "next-env.d.ts"', () => {
    expect(tsconfig.include).toContain('next-env.d.ts');
  });

  it('include contains "**/*.ts"', () => {
    expect(tsconfig.include).toContain('**/*.ts');
  });

  it('include contains "**/*.tsx"', () => {
    expect(tsconfig.include).toContain('**/*.tsx');
  });

  it('include contains ".next/types/**/*.ts"', () => {
    expect(tsconfig.include).toContain('.next/types/**/*.ts');
  });

  it('include has exactly 4 entries', () => {
    expect(tsconfig.include).toHaveLength(4);
  });
});

// ---------------------------------------------------------------------------
// 4. exclude
// ---------------------------------------------------------------------------

describe('exclude', () => {
  it('exclude field exists', () => {
    expect(tsconfig.exclude).toBeDefined();
    expect(Array.isArray(tsconfig.exclude)).toBe(true);
  });

  it('exclude contains "node_modules"', () => {
    expect(tsconfig.exclude).toContain('node_modules');
  });
});

// ---------------------------------------------------------------------------
// 5. JSON validity and file existence
// ---------------------------------------------------------------------------

describe('tsconfig.json file', () => {
  it('is valid JSON and parseable', () => {
    const raw = fs.readFileSync(TSCONFIG_PATH, 'utf-8');
    expect(() => JSON.parse(raw)).not.toThrow();
  });

  it('file exists at expected location', () => {
    expect(fs.existsSync(TSCONFIG_PATH)).toBe(true);
  });
});
