/**
 * Tests for package.json
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that package.json conforms to the specification in
 * prompts/package_json_json.prompt.
 */

import * as fs from 'fs';
import * as path from 'path';

const PKG_PATH = path.resolve(__dirname, '..', 'package.json');

interface PackageJson {
  name: string;
  version: string;
  private: boolean;
  engines: Record<string, string>;
  scripts: Record<string, string>;
  dependencies: Record<string, string>;
  devDependencies: Record<string, string>;
  [key: string]: unknown;
}

let pkg: PackageJson;

beforeAll(() => {
  const raw = fs.readFileSync(PKG_PATH, 'utf-8');
  pkg = JSON.parse(raw) as PackageJson;
});

// ---------------------------------------------------------------------------
// 1. Top-level metadata
// ---------------------------------------------------------------------------

describe('package.json metadata', () => {
  it('name is "video-editor-pdd"', () => {
    expect(pkg.name).toBe('video-editor-pdd');
  });

  it('version is "0.1.0"', () => {
    expect(pkg.version).toBe('0.1.0');
  });

  it('private is true', () => {
    expect(pkg.private).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// 2. engines
// ---------------------------------------------------------------------------

describe('engines', () => {
  it('engines field exists', () => {
    expect(pkg.engines).toBeDefined();
    expect(typeof pkg.engines).toBe('object');
  });

  it('node engine is ">=20"', () => {
    expect(pkg.engines['node']).toBe('>=20');
  });
});

// ---------------------------------------------------------------------------
// 3. scripts
// ---------------------------------------------------------------------------

describe('scripts', () => {
  it('scripts field exists', () => {
    expect(pkg.scripts).toBeDefined();
  });

  it('dev script is "next dev"', () => {
    expect(pkg.scripts['dev']).toBe('next dev');
  });

  it('build script is "next build"', () => {
    expect(pkg.scripts['build']).toBe('next build');
  });

  it('start script is "next start"', () => {
    expect(pkg.scripts['start']).toBe('next start');
  });

  it('lint script is "next lint"', () => {
    expect(pkg.scripts['lint']).toBe('next lint');
  });

  it('has exactly 4 scripts', () => {
    const scriptKeys = Object.keys(pkg.scripts);
    expect(scriptKeys).toHaveLength(4);
  });
});

// ---------------------------------------------------------------------------
// 4. Core dependencies
// ---------------------------------------------------------------------------

describe('dependencies', () => {
  it('dependencies field exists', () => {
    expect(pkg.dependencies).toBeDefined();
    expect(typeof pkg.dependencies).toBe('object');
  });

  const requiredDeps: Record<string, string> = {
    next: '^15.0.0',
    react: '^19.0.0',
    'react-dom': '^19.0.0',
    'better-sqlite3': '^11.0.0',
    '@google/generative-ai': '^0.21.0',
    '@remotion/renderer': '^4.0.0',
    remotion: '^4.0.0',
    'wavesurfer.js': '^7.0.0',
    '@codemirror/basic-setup': '^0.20.0',
    '@codemirror/view': '^6.0.0',
    '@codemirror/state': '^6.0.0',
    '@codemirror/lang-markdown': '^6.0.0',
    zod: '^3.0.0',
  };

  for (const [name, version] of Object.entries(requiredDeps)) {
    it(`has dependency "${name}": "${version}"`, () => {
      expect(pkg.dependencies[name]).toBe(version);
    });
  }

  it('has exactly 13 core dependencies', () => {
    expect(Object.keys(pkg.dependencies)).toHaveLength(13);
  });

  it('uses "^" (caret) version ranges for all dependencies', () => {
    for (const [name, version] of Object.entries(pkg.dependencies)) {
      expect(version).toMatch(/^\^/, `${name} should use caret range`);
    }
  });
});

// ---------------------------------------------------------------------------
// 5. devDependencies
// ---------------------------------------------------------------------------

describe('devDependencies', () => {
  it('devDependencies field exists', () => {
    expect(pkg.devDependencies).toBeDefined();
    expect(typeof pkg.devDependencies).toBe('object');
  });

  const requiredDevDeps: Record<string, string> = {
    typescript: '^5.0.0',
    '@types/node': '^20.0.0',
    '@types/react': '^19.0.0',
    '@types/react-dom': '^19.0.0',
    '@types/better-sqlite3': '^7.0.0',
    tailwindcss: '^4.0.0',
    eslint: '^8.0.0',
    'eslint-config-next': '^15.0.0',
  };

  for (const [name, version] of Object.entries(requiredDevDeps)) {
    it(`has devDependency "${name}": "${version}"`, () => {
      expect(pkg.devDependencies[name]).toBe(version);
    });
  }

  it('has exactly 8 devDependencies', () => {
    expect(Object.keys(pkg.devDependencies)).toHaveLength(8);
  });

  it('uses "^" (caret) version ranges for all devDependencies', () => {
    for (const [name, version] of Object.entries(pkg.devDependencies)) {
      expect(version).toMatch(/^\^/, `${name} should use caret range`);
    }
  });
});

// ---------------------------------------------------------------------------
// 6. Exclusions (Tailwind v4 CSS-first, no legacy config packages)
// ---------------------------------------------------------------------------

describe('excluded packages', () => {
  it('does not include postcss in dependencies', () => {
    expect(pkg.dependencies['postcss']).toBeUndefined();
  });

  it('does not include postcss in devDependencies', () => {
    expect(pkg.devDependencies['postcss']).toBeUndefined();
  });

  it('does not include autoprefixer in dependencies', () => {
    expect(pkg.dependencies['autoprefixer']).toBeUndefined();
  });

  it('does not include autoprefixer in devDependencies', () => {
    expect(pkg.devDependencies['autoprefixer']).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 7. JSON validity and parsability
// ---------------------------------------------------------------------------

describe('package.json file', () => {
  it('is valid JSON and parseable', () => {
    const raw = fs.readFileSync(PKG_PATH, 'utf-8');
    expect(() => JSON.parse(raw)).not.toThrow();
  });

  it('file exists at expected location', () => {
    expect(fs.existsSync(PKG_PATH)).toBe(true);
  });
});
