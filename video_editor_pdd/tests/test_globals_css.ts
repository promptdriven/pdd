/**
 * Tests for app/globals.css
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that globals.css conforms to the specification in
 * prompts/globals_css_css.prompt.
 */

import * as fs from 'fs';
import * as path from 'path';

const CSS_PATH = path.resolve(__dirname, '..', 'app', 'globals.css');

let css: string;

beforeAll(() => {
  css = fs.readFileSync(CSS_PATH, 'utf-8');
});

// ---------------------------------------------------------------------------
// 1. File existence and basic structure
// ---------------------------------------------------------------------------

describe('globals.css file', () => {
  it('file exists at expected location', () => {
    expect(fs.existsSync(CSS_PATH)).toBe(true);
  });

  it('is non-empty', () => {
    expect(css.trim().length).toBeGreaterThan(0);
  });
});

// ---------------------------------------------------------------------------
// 2. Tailwind v4 CSS-first import
// ---------------------------------------------------------------------------

describe('Tailwind v4 CSS-first import', () => {
  it('contains @import "tailwindcss" directive', () => {
    expect(css).toMatch(/@import\s+['"]tailwindcss['"]/);
  });

  it('@import "tailwindcss" is the first non-comment line', () => {
    const lines = css.split('\n');
    let firstNonCommentLine = '';
    let inBlockComment = false;
    for (const line of lines) {
      const trimmed = line.trim();
      if (inBlockComment) {
        if (trimmed.includes('*/')) {
          inBlockComment = false;
        }
        continue;
      }
      if (trimmed.startsWith('/*')) {
        if (!trimmed.includes('*/')) {
          inBlockComment = true;
        }
        continue;
      }
      if (trimmed === '' || trimmed.startsWith('//')) {
        continue;
      }
      firstNonCommentLine = trimmed;
      break;
    }
    expect(firstNonCommentLine).toMatch(/@import\s+['"]tailwindcss['"]/);
  });
});

// ---------------------------------------------------------------------------
// 3. @theme block with custom color tokens
// ---------------------------------------------------------------------------

describe('@theme block', () => {
  it('contains an @theme block', () => {
    expect(css).toMatch(/@theme\s*\{/);
  });

  // Extract @theme block content for detailed checks
  function getThemeBlock(): string {
    const match = css.match(/@theme\s*\{([\s\S]*?)\n\}/);
    return match ? match[1] : '';
  }

  // Sidebar
  it('defines --color-sidebar: #0f172a', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-sidebar\s*:\s*#0f172a/);
  });

  // Panel & Layout
  it('defines --color-panel: #1e293b', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-panel\s*:\s*#1e293b/);
  });

  it('defines --color-border: #334155', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-border\s*:\s*#334155/);
  });

  // Stage status badge colors
  it('defines --color-stage-done: #22c55e', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-stage-done\s*:\s*#22c55e/);
  });

  it('defines --color-stage-running: #f59e0b', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-stage-running\s*:\s*#f59e0b/);
  });

  it('defines --color-stage-error: #ef4444', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-stage-error\s*:\s*#ef4444/);
  });

  it('defines --color-stage-not-started: #64748b', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-stage-not-started\s*:\s*#64748b/);
  });

  // Annotation severity colors
  it('defines --color-severity-critical: #ef4444', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-severity-critical\s*:\s*#ef4444/);
  });

  it('defines --color-severity-major: #f97316', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-severity-major\s*:\s*#f97316/);
  });

  it('defines --color-severity-minor: #eab308', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-severity-minor\s*:\s*#eab308/);
  });

  it('defines --color-severity-pass: #22c55e', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--color-severity-pass\s*:\s*#22c55e/);
  });

  // All color tokens use --color-* naming convention
  it('all custom color properties use --color-* naming convention', () => {
    const theme = getThemeBlock();
    const colorProps = theme.match(/--color-[\w-]+\s*:/g) || [];
    // We expect at least the 11 specified colors
    expect(colorProps.length).toBeGreaterThanOrEqual(11);
  });

  // Animation token
  it('defines --animate-stage-running animation token', () => {
    const theme = getThemeBlock();
    expect(theme).toMatch(/--animate-stage-running\s*:/);
  });
});

// ---------------------------------------------------------------------------
// 4. @keyframes pulse-badge animation
// ---------------------------------------------------------------------------

describe('@keyframes pulse-badge', () => {
  it('defines @keyframes pulse-badge', () => {
    expect(css).toMatch(/@keyframes\s+pulse-badge/);
  });

  it('pulse-badge has opacity: 1 at 0% and 100%', () => {
    // Extract keyframes block
    const kfMatch = css.match(/@keyframes\s+pulse-badge\s*\{([\s\S]*?)\n\}/);
    expect(kfMatch).not.toBeNull();
    const kfContent = kfMatch![1];
    expect(kfContent).toMatch(/0%/);
    expect(kfContent).toMatch(/100%/);
    expect(kfContent).toMatch(/opacity\s*:\s*1/);
  });

  it('pulse-badge has opacity: 0.5 at 50%', () => {
    const kfMatch = css.match(/@keyframes\s+pulse-badge\s*\{([\s\S]*?)\n\}/);
    expect(kfMatch).not.toBeNull();
    const kfContent = kfMatch![1];
    expect(kfContent).toMatch(/50%/);
    expect(kfContent).toMatch(/opacity\s*:\s*0\.5/);
  });
});

// ---------------------------------------------------------------------------
// 5. @layer base — body defaults
// ---------------------------------------------------------------------------

describe('@layer base — body defaults', () => {
  function getBaseLayer(): string {
    const match = css.match(/@layer\s+base\s*\{([\s\S]*?)\n\}/);
    return match ? match[1] : '';
  }

  it('contains @layer base block', () => {
    expect(css).toMatch(/@layer\s+base\s*\{/);
  });

  it('body uses theme(--color-panel) for background-color', () => {
    const base = getBaseLayer();
    expect(base).toMatch(/body\s*\{[\s\S]*?background-color\s*:\s*theme\(--color-panel\)/);
  });

  it('body text color is #e2e8f0', () => {
    const base = getBaseLayer();
    expect(base).toMatch(/body\s*\{[\s\S]*?color\s*:\s*#e2e8f0/);
  });

  it('body font-family includes ui-monospace', () => {
    const base = getBaseLayer();
    expect(base).toMatch(/body\s*\{[\s\S]*?font-family\s*:.*ui-monospace/);
  });

  it('body font-family includes Cascadia Code', () => {
    const base = getBaseLayer();
    expect(base).toMatch(/body\s*\{[\s\S]*?font-family\s*:.*Cascadia Code/);
  });

  it('body font-family includes monospace fallback', () => {
    const base = getBaseLayer();
    expect(base).toMatch(/body\s*\{[\s\S]*?font-family\s*:.*monospace/);
  });
});

// ---------------------------------------------------------------------------
// 6. @layer base — scrollbar styling
// ---------------------------------------------------------------------------

describe('@layer base — scrollbar styling', () => {
  it('contains ::-webkit-scrollbar pseudo-element', () => {
    expect(css).toMatch(/::-webkit-scrollbar\s*\{/);
  });

  it('contains ::-webkit-scrollbar-track pseudo-element', () => {
    expect(css).toMatch(/::-webkit-scrollbar-track\s*\{/);
  });

  it('contains ::-webkit-scrollbar-thumb pseudo-element', () => {
    expect(css).toMatch(/::-webkit-scrollbar-thumb\s*\{/);
  });

  it('scrollbar-track uses panel background via theme(--color-panel)', () => {
    // Find the track rule
    const trackMatch = css.match(/::-webkit-scrollbar-track\s*\{([\s\S]*?)\}/);
    expect(trackMatch).not.toBeNull();
    expect(trackMatch![1]).toMatch(/background-color\s*:\s*theme\(--color-panel\)/);
  });

  it('scrollbar-thumb uses border color via theme(--color-border)', () => {
    // Find the thumb rule (first one, not hover)
    const thumbMatches = css.match(/::-webkit-scrollbar-thumb\s*\{([\s\S]*?)\}/);
    expect(thumbMatches).not.toBeNull();
    expect(thumbMatches![1]).toMatch(/background-color\s*:\s*theme\(--color-border\)/);
  });

  it('scrollbar width and height are thin (6px)', () => {
    const scrollbarMatch = css.match(/::-webkit-scrollbar\s*\{([\s\S]*?)\}/);
    expect(scrollbarMatch).not.toBeNull();
    const content = scrollbarMatch![1];
    expect(content).toMatch(/width\s*:\s*6px/);
    expect(content).toMatch(/height\s*:\s*6px/);
  });
});

// ---------------------------------------------------------------------------
// 7. @layer utilities — SSE log panel
// ---------------------------------------------------------------------------

describe('@layer utilities — SSE log panel', () => {
  it('contains @layer utilities block', () => {
    expect(css).toMatch(/@layer\s+utilities\s*\{/);
  });

  it('defines .sse-log-panel class', () => {
    expect(css).toMatch(/\.sse-log-panel\s*\{/);
  });

  function getSseLogPanel(): string {
    const match = css.match(/\.sse-log-panel\s*\{([\s\S]*?)\}/);
    return match ? match[1] : '';
  }

  it('SSE log panel uses monospace font-family', () => {
    const panel = getSseLogPanel();
    expect(panel).toMatch(/font-family\s*:.*ui-monospace/);
    expect(panel).toMatch(/font-family\s*:.*monospace/);
  });

  it('SSE log panel has small text size (0.75rem)', () => {
    const panel = getSseLogPanel();
    expect(panel).toMatch(/font-size\s*:\s*0\.75rem/);
  });

  it('SSE log panel disables wrapping (white-space: nowrap)', () => {
    const panel = getSseLogPanel();
    expect(panel).toMatch(/white-space\s*:\s*nowrap/);
  });

  it('SSE log panel has overflow-x: auto for horizontal scrolling', () => {
    const panel = getSseLogPanel();
    expect(panel).toMatch(/overflow-x\s*:\s*auto/);
  });
});

// ---------------------------------------------------------------------------
// 8. No tailwind.config.js (CSS-first approach)
// ---------------------------------------------------------------------------

describe('CSS-first configuration (no tailwind.config.js)', () => {
  it('no tailwind.config.js exists in project root', () => {
    const configPath = path.resolve(__dirname, '..', 'tailwind.config.js');
    expect(fs.existsSync(configPath)).toBe(false);
  });

  it('no tailwind.config.ts exists in project root', () => {
    const configPath = path.resolve(__dirname, '..', 'tailwind.config.ts');
    expect(fs.existsSync(configPath)).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// 9. Dark theme verification — background tokens are dark slate shades
// ---------------------------------------------------------------------------

describe('dark theme color tokens', () => {
  function getThemeBlock(): string {
    const match = css.match(/@theme\s*\{([\s\S]*?)\n\}/);
    return match ? match[1] : '';
  }

  it('sidebar color (#0f172a) is a dark shade', () => {
    const theme = getThemeBlock();
    const match = theme.match(/--color-sidebar\s*:\s*(#[0-9a-fA-F]{6})/);
    expect(match).not.toBeNull();
    // Verify it's dark by checking the hex value components are low
    const hex = match![1];
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    const brightness = (r + g + b) / 3;
    expect(brightness).toBeLessThan(80); // Dark shade
  });

  it('panel color (#1e293b) is a dark shade', () => {
    const theme = getThemeBlock();
    const match = theme.match(/--color-panel\s*:\s*(#[0-9a-fA-F]{6})/);
    expect(match).not.toBeNull();
    const hex = match![1];
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    const brightness = (r + g + b) / 3;
    expect(brightness).toBeLessThan(80);
  });

  it('border color (#334155) is a dark shade', () => {
    const theme = getThemeBlock();
    const match = theme.match(/--color-border\s*:\s*(#[0-9a-fA-F]{6})/);
    expect(match).not.toBeNull();
    const hex = match![1];
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    const brightness = (r + g + b) / 3;
    expect(brightness).toBeLessThan(100);
  });
});
