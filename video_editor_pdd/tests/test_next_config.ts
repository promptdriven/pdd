/**
 * Tests for next.config.ts
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that next.config.ts conforms to the specification in
 * prompts/next_config_typescript.prompt.
 *
 * Specification requirements:
 *   1. TypeScript config format: `import type { NextConfig } from 'next'` with
 *      `export default nextConfig`.
 *   2. serverExternalPackages: ['better-sqlite3'] for native SQLite addon.
 *   3. experimental.serverActions.bodySizeLimit: '10mb' for large uploads.
 *   4. Custom SSE headers for /api/pipeline/:path* and /api/jobs/:path*:
 *        Cache-Control: no-cache, no-transform
 *        X-Accel-Buffering: no
 *   5. Dev-only webpack override to ignore remotion/outputs/.git in watch.
 *   6. No experimental.appDir.
 *   7. Minimal config — no reactStrictMode or unlisted settings.
 */

import * as fs from 'fs';
import * as path from 'path';

// ---------------------------------------------------------------------------
// Load the config module
// ---------------------------------------------------------------------------

// eslint-disable-next-line @typescript-eslint/no-var-requires
const configModule = require('../next.config');

// Handle both ESM default export (compiled by ts-jest) and plain object
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const nextConfig: Record<string, any> =
  configModule.default !== undefined ? configModule.default : configModule;

// ---------------------------------------------------------------------------
// Helper types matching the NextConfig headers() return shape
// ---------------------------------------------------------------------------

interface HeaderEntry {
  key: string;
  value: string;
}

interface HeaderRule {
  source: string;
  headers: HeaderEntry[];
}

// ---------------------------------------------------------------------------
// 1. Module structure
// ---------------------------------------------------------------------------

describe('next.config.ts — module structure', () => {
  it('exports a non-null config object as default export', () => {
    expect(nextConfig).toBeDefined();
    expect(typeof nextConfig).toBe('object');
    expect(nextConfig).not.toBeNull();
  });

  it('source file uses TypeScript config format (import type from next)', () => {
    const srcPath = path.resolve(__dirname, '..', 'next.config.ts');
    const source = fs.readFileSync(srcPath, 'utf-8');
    expect(source).toMatch(/import type \{ NextConfig \} from 'next'/);
  });

  it('source file uses const nextConfig: NextConfig = { ... }', () => {
    const srcPath = path.resolve(__dirname, '..', 'next.config.ts');
    const source = fs.readFileSync(srcPath, 'utf-8');
    expect(source).toMatch(/const nextConfig:\s*NextConfig\s*=/);
  });

  it('source file uses export default nextConfig', () => {
    const srcPath = path.resolve(__dirname, '..', 'next.config.ts');
    const source = fs.readFileSync(srcPath, 'utf-8');
    expect(source).toMatch(/export default nextConfig/);
  });
});

// ---------------------------------------------------------------------------
// 2. serverExternalPackages
// ---------------------------------------------------------------------------

describe('next.config.ts — serverExternalPackages', () => {
  it('serverExternalPackages is defined', () => {
    expect(nextConfig.serverExternalPackages).toBeDefined();
  });

  it('serverExternalPackages is an array', () => {
    expect(Array.isArray(nextConfig.serverExternalPackages)).toBe(true);
  });

  it('serverExternalPackages contains better-sqlite3', () => {
    expect(nextConfig.serverExternalPackages).toContain('better-sqlite3');
  });

  it('serverExternalPackages contains exactly one entry', () => {
    expect(nextConfig.serverExternalPackages).toHaveLength(1);
  });
});

// ---------------------------------------------------------------------------
// 3. experimental.serverActions.bodySizeLimit
// ---------------------------------------------------------------------------

describe('next.config.ts — experimental.serverActions.bodySizeLimit', () => {
  it('experimental is defined', () => {
    expect(nextConfig.experimental).toBeDefined();
    expect(typeof nextConfig.experimental).toBe('object');
  });

  it('experimental.serverActions is defined', () => {
    expect(nextConfig.experimental.serverActions).toBeDefined();
    expect(typeof nextConfig.experimental.serverActions).toBe('object');
  });

  it('experimental.serverActions.bodySizeLimit is "10mb"', () => {
    expect(nextConfig.experimental.serverActions.bodySizeLimit).toBe('10mb');
  });
});

// ---------------------------------------------------------------------------
// 4. SSE headers function
// ---------------------------------------------------------------------------

describe('next.config.ts — headers() function', () => {
  it('headers is defined as a function', () => {
    expect(typeof nextConfig.headers).toBe('function');
  });

  it('headers() returns a Promise', () => {
    const result = nextConfig.headers();
    expect(result).toBeInstanceOf(Promise);
    // Clean up the promise
    return result;
  });

  describe('headers() resolved value', () => {
    let headerRules: HeaderRule[];

    beforeAll(async () => {
      headerRules = await nextConfig.headers();
    });

    it('returns an array', () => {
      expect(Array.isArray(headerRules)).toBe(true);
    });

    it('returns exactly 2 header rule entries', () => {
      expect(headerRules).toHaveLength(2);
    });

    // ── /api/pipeline/:path* ──────────────────────────────────────────────

    describe('/api/pipeline/:path* header rule', () => {
      let pipelineRule: HeaderRule;

      beforeAll(() => {
        pipelineRule = headerRules.find(
          (r) => r.source === '/api/pipeline/:path*',
        ) as HeaderRule;
      });

      it('has source "/api/pipeline/:path*"', () => {
        expect(pipelineRule).toBeDefined();
        expect(pipelineRule.source).toBe('/api/pipeline/:path*');
      });

      it('headers array has exactly 2 entries', () => {
        expect(Array.isArray(pipelineRule.headers)).toBe(true);
        expect(pipelineRule.headers).toHaveLength(2);
      });

      it('has Cache-Control: no-cache, no-transform', () => {
        const h = pipelineRule.headers.find((e) => e.key === 'Cache-Control');
        expect(h).toBeDefined();
        expect(h!.value).toBe('no-cache, no-transform');
      });

      it('has X-Accel-Buffering: no', () => {
        const h = pipelineRule.headers.find(
          (e) => e.key === 'X-Accel-Buffering',
        );
        expect(h).toBeDefined();
        expect(h!.value).toBe('no');
      });
    });

    // ── /api/jobs/:path* ─────────────────────────────────────────────────

    describe('/api/jobs/:path* header rule', () => {
      let jobsRule: HeaderRule;

      beforeAll(() => {
        jobsRule = headerRules.find(
          (r) => r.source === '/api/jobs/:path*',
        ) as HeaderRule;
      });

      it('has source "/api/jobs/:path*"', () => {
        expect(jobsRule).toBeDefined();
        expect(jobsRule.source).toBe('/api/jobs/:path*');
      });

      it('headers array has exactly 2 entries', () => {
        expect(Array.isArray(jobsRule.headers)).toBe(true);
        expect(jobsRule.headers).toHaveLength(2);
      });

      it('has Cache-Control: no-cache, no-transform', () => {
        const h = jobsRule.headers.find((e) => e.key === 'Cache-Control');
        expect(h).toBeDefined();
        expect(h!.value).toBe('no-cache, no-transform');
      });

      it('has X-Accel-Buffering: no', () => {
        const h = jobsRule.headers.find(
          (e) => e.key === 'X-Accel-Buffering',
        );
        expect(h).toBeDefined();
        expect(h!.value).toBe('no');
      });
    });

    // ── header entry shape ────────────────────────────────────────────────

    it('every header entry has { key: string, value: string } shape', () => {
      for (const rule of headerRules) {
        for (const entry of rule.headers) {
          expect(typeof entry.key).toBe('string');
          expect(typeof entry.value).toBe('string');
          expect(entry.key.length).toBeGreaterThan(0);
        }
      }
    });
  });
});

// ---------------------------------------------------------------------------
// 5. Prohibited settings (minimalism requirement)
// ---------------------------------------------------------------------------

describe('next.config.ts — prohibited settings', () => {
  it('defines webpack as a dev-only watch-options override', () => {
    expect(nextConfig.webpack).toBeDefined();
    expect(typeof nextConfig.webpack).toBe('function');
  });

  it('does not enable experimental.appDir (default in Next.js 15)', () => {
    if (nextConfig.experimental) {
      expect(nextConfig.experimental.appDir).toBeUndefined();
    }
    // If experimental is undefined, appDir is also absent — pass.
  });

  it('does not define reactStrictMode', () => {
    expect(nextConfig.reactStrictMode).toBeUndefined();
  });

  it('does not define any other top-level keys beyond the required set', () => {
    const allowedKeys = new Set([
      'eslint',
      'serverExternalPackages',
      'experimental',
      'headers',
      'webpack',
    ]);
    const actualKeys = Object.keys(nextConfig);
    for (const key of actualKeys) {
      expect(allowedKeys.has(key)).toBe(true);
    }
  });
});

// ---------------------------------------------------------------------------
// 6. File-level checks
// ---------------------------------------------------------------------------

describe('next.config.ts — file-level checks', () => {
  const CONFIG_PATH = path.resolve(__dirname, '..', 'next.config.ts');

  it('file exists at project root', () => {
    expect(fs.existsSync(CONFIG_PATH)).toBe(true);
  });

  it('file is named next.config.ts (TypeScript, not .js or .mjs)', () => {
    expect(CONFIG_PATH.endsWith('.ts')).toBe(true);
  });

  it('source contains webpack override limited to dev watchOptions', () => {
    const source = fs.readFileSync(CONFIG_PATH, 'utf-8');
    // webpack key exists for dev-only watch option overrides
    expect(source).toMatch(/\bwebpack\s*:/);
    // It should only modify watchOptions in dev mode
    expect(source).toMatch(/watchOptions/);
    expect(source).toMatch(/\bdev\b/);
  });

  it('source does not contain reactStrictMode', () => {
    const source = fs.readFileSync(CONFIG_PATH, 'utf-8');
    expect(source).not.toMatch(/\breactStrictMode\b/);
  });

  it('source does not contain experimental.appDir', () => {
    const source = fs.readFileSync(CONFIG_PATH, 'utf-8');
    expect(source).not.toMatch(/\bappDir\b/);
  });
});
