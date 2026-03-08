import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

/**
 * Navigate to Stage 6 (Spec Generation) via the sidebar.
 * Uses 3-attempt retry with sidebar `div.cursor-pointer.nth(5)`.
 */
async function navigateToStage6(page: import('@playwright/test').Page) {
  await page.goto('/');
  await page.waitForLoadState('networkidle');

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });

  // Wait for React hydration
  await page.waitForTimeout(1000);

  const heading = page.locator('h2', { hasText: 'Stage 6' });

  // Attempt 1: Playwright click
  await sidebar.locator('div.cursor-pointer').nth(5).click();
  try {
    await expect(heading).toBeVisible({ timeout: 3000 });
  } catch {
    // Attempt 2: JS click
    await page.waitForTimeout(500);
    await page.evaluate(() => {
      const items = document.querySelectorAll('aside div.cursor-pointer');
      if (items[5]) (items[5] as HTMLElement).click();
    });
    try {
      await expect(heading).toBeVisible({ timeout: 3000 });
    } catch {
      // Attempt 3: force click after longer wait
      await page.waitForTimeout(1000);
      await sidebar.locator('div.cursor-pointer').nth(5).click({ force: true });
      await expect(heading).toBeVisible({ timeout: 10000 });
    }
  }

  await page.waitForTimeout(500);
}

/**
 * Navigate to Stage 6 with mocked GET /api/pipeline/specs/list and optional file content.
 * Sets up route mocks BEFORE navigating so they're in place for the fetch.
 */
async function navigateWithMockedSpecs(
  page: import('@playwright/test').Page,
  sections: Array<{
    id: string;
    label: string;
    files: Array<{ path: string; exists: boolean; firstLine?: string }>;
  }>,
  fileContentOverrides: Record<string, string> = {},
  scriptContent = '# Mock Script\n\n## Cold Open\n\n**NARRATOR:**\nA mocked narration line.',
) {
  await page.route('**/api/pipeline/specs/list', (route) => {
    return route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ sections }),
    });
  });

  // Mock file GET for editor
  await page.route('**/api/pipeline/specs/file**', (route) => {
    if (route.request().method() === 'GET') {
      const url = new URL(route.request().url());
      const filePath = url.searchParams.get('path') ?? '';
      const content = fileContentOverrides[filePath] ?? '# Spec Content\n\nSome markdown body here.';
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content }),
      });
    }
    return route.fallback();
  });

  await page.route('**/api/project/script', (route) => {
    return route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ content: scriptContent }),
    });
  });

  await navigateToStage6(page);
  await page.waitForTimeout(500);
}

const DEFAULT_SECTIONS = [
  {
    id: 'cold-open',
    label: 'Cold Open',
    files: [
      { path: 'specs/00-cold-open/spec.md', exists: true, firstLine: '[Remotion] Title Card' },
      { path: 'specs/00-cold-open/veo.md', exists: false },
    ],
  },
  {
    id: 'part-1',
    label: 'Part 1: Economics',
    files: [
      { path: 'specs/01-part-1/spec.md', exists: true, firstLine: '[veo:aerial] flyover' },
    ],
  },
];

test.describe('Stage 6: Interactive QA - Comprehensive Feature Testing', () => {
  // =========================================================================
  // Group A: Initial Load & UI Elements (9 tests)
  // =========================================================================
  test.describe('Group A: Initial load & UI elements', () => {
    test('A1: "Stage 6 — Spec Generation" heading visible', async ({ page }) => {
      await navigateToStage6(page);
      const heading = page.locator('h2', { hasText: 'Stage 6' });
      await expect(heading).toBeVisible();
      await expect(heading).toHaveText(/Stage 6 — Spec Generation/);
    });

    test('A2: "Generate All Specs" button visible with bg-indigo-600', async ({ page }) => {
      await navigateToStage6(page);
      const btn = page.locator('button', { hasText: 'Generate All Specs' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-indigo-600');
    });

    test('A3: "Continue →" button visible with border-slate-600', async ({ page }) => {
      await navigateToStage6(page);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('border-slate-600');
    });

    test('A4: Section accordion cards render from mocked data (2 sections)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      await expect(page.locator('button', { hasText: 'Cold Open' })).toBeVisible();
      await expect(page.locator('button', { hasText: 'Part 1: Economics' })).toBeVisible();
    });

    test('A5: Section label text with font-medium text-slate-200', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const sectionBtn = page.locator('button', { hasText: 'Cold Open' });
      await expect(sectionBtn).toBeVisible();
      const cls = await sectionBtn.getAttribute('class') ?? '';
      expect(cls).toContain('font-medium');
      expect(cls).toContain('text-slate-200');
    });

    test('A6: "Spec Generation Logs" details element present', async ({ page }) => {
      await navigateToStage6(page);
      await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
      await page.waitForTimeout(300);
      const logsSummary = page.locator('summary', { hasText: 'Spec Generation Logs' });
      await expect(logsSummary).toBeVisible();
    });

    test('A7: Loading state shows "Loading spec list…" during slow fetch', async ({ page }) => {
      await page.route('**/api/pipeline/specs/list', async (route) => {
        await new Promise((resolve) => setTimeout(resolve, 1500));
        await route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ sections: [] }),
        });
      });

      await navigateToStage6(page);
      await expect(page.locator('text=Loading spec list…')).toBeVisible({ timeout: 2000 });
    });

    test('A8: Empty state shows "No spec sections found." with empty sections', async ({ page }) => {
      await navigateWithMockedSpecs(page, []);
      await expect(page.locator('text=No spec sections found.')).toBeVisible();
    });

    test('A9: screenshot — full initial state', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-A9-initial-state.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group B: Accordion & Collapse (8 tests)
  // =========================================================================
  test.describe('Group B: Accordion & collapse', () => {
    test('B1: Sections default to expanded (▾ arrow visible)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });
      await expect(toggleBtn).toBeVisible();
      await expect(toggleBtn.locator('text=▾')).toBeVisible();
    });

    test('B2: Clicking toggle collapses section (▸ arrow visible)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▸')).toBeVisible();
    });

    test('B3: Collapsed section hides file table', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      // File table should be visible initially (section expanded)
      const specPath = page.locator('text=specs/00-cold-open/spec.md');
      await expect(specPath).toBeVisible();

      // Collapse
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });
      await toggleBtn.click();
      await page.waitForTimeout(300);

      // File table should now be hidden
      await expect(specPath).not.toBeVisible();
    });

    test('B4: Clicking again re-expands section', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });

      // Collapse
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▸')).toBeVisible();

      // Re-expand
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▾')).toBeVisible();
      await expect(page.locator('text=specs/00-cold-open/spec.md')).toBeVisible();
    });

    test('B5: Multiple sections expand/collapse independently', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const btn1 = page.locator('button', { hasText: 'Cold Open' });
      const btn2 = page.locator('button', { hasText: 'Part 1: Economics' });

      // Collapse Cold Open only
      await btn1.click();
      await page.waitForTimeout(300);

      // Cold Open collapsed, Part 1 still expanded
      await expect(btn1.locator('text=▸')).toBeVisible();
      await expect(btn2.locator('text=▾')).toBeVisible();
      await expect(page.locator('text=specs/01-part-1/spec.md')).toBeVisible();
    });

    test('B6: localStorage is updated on toggle', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });

      // Collapse Cold Open
      await toggleBtn.click();
      await page.waitForTimeout(300);

      // Check localStorage
      const stored = await page.evaluate(() => {
        return localStorage.getItem('spec-sections-expanded');
      });
      expect(stored).toBeTruthy();
      const parsed = JSON.parse(stored!);
      expect(parsed['cold-open']).toBe(false);
      expect(parsed['part-1']).toBe(true);
    });

    test('B7: localStorage restored on re-navigation', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      // Collapse Cold Open
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▸')).toBeVisible();

      // Navigate away to Setup
      const sidebar = page.locator('aside');
      await sidebar.locator('div.cursor-pointer').nth(0).click();
      await page.waitForTimeout(500);

      // Navigate back to Stage 6
      await sidebar.locator('div.cursor-pointer').nth(5).click();
      await page.waitForTimeout(1500);

      // Cold Open should still be collapsed
      const toggleBtnAfter = page.locator('button', { hasText: 'Cold Open' });
      await expect(toggleBtnAfter).toBeVisible({ timeout: 5000 });
      await expect(toggleBtnAfter.locator('text=▸')).toBeVisible();
    });

    test('B8: screenshot — one expanded, one collapsed', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      // Collapse Cold Open, leave Part 1 expanded
      const toggleBtn = page.locator('button', { hasText: 'Cold Open' });
      await toggleBtn.click();
      await page.waitForTimeout(300);

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-B8-accordion-state.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group C: File Table & Badges (9 tests)
  // =========================================================================
  test.describe('Group C: File table & badges', () => {
    const badgeSections = [
      {
        id: 'badges',
        label: 'Badge Test Section',
        files: [
          { path: 'specs/remotion.md', exists: true, firstLine: '[Remotion] Title Card' },
          { path: 'specs/veo.md', exists: true, firstLine: '[veo:aerial] flyover' },
          { path: 'specs/title.md', exists: true, firstLine: '[title:Part 1] Section Header' },
          { path: 'specs/split.md', exists: true, firstLine: '[split:left] Left panel' },
          { path: 'specs/plain.md', exists: false },
        ],
      },
    ];

    test('C1: Table headers — Type, Path, Status, Actions', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      await expect(page.locator('th', { hasText: 'Type' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Path' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Status' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Actions' }).first()).toBeVisible();
    });

    test('C2: File path displayed with font-mono text-xs text-slate-300', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const pathCell = page.locator('td.font-mono', { hasText: 'specs/00-cold-open/spec.md' });
      await expect(pathCell).toBeVisible();
      const cls = await pathCell.getAttribute('class') ?? '';
      expect(cls).toContain('font-mono');
      expect(cls).toContain('text-xs');
      expect(cls).toContain('text-slate-300');
    });

    test('C3: "exists" status shown in green (text-green-600)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const existsSpan = page.locator('span.text-green-600', { hasText: 'exists' });
      await expect(existsSpan.first()).toBeVisible();
    });

    test('C4: "missing" status shown in red (text-red-500)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const missingSpan = page.locator('span.text-red-500', { hasText: 'missing' });
      await expect(missingSpan.first()).toBeVisible();
    });

    test('C5: [Remotion] badge with blue styling', async ({ page }) => {
      await navigateWithMockedSpecs(page, badgeSections);
      const badge = page.locator('span', { hasText: '[Remotion]' });
      await expect(badge).toBeVisible();
      const cls = await badge.getAttribute('class') ?? '';
      expect(cls).toContain('blue');
    });

    test('C6: [veo:...] badge with purple styling', async ({ page }) => {
      await navigateWithMockedSpecs(page, badgeSections);
      const badge = page.locator('span').filter({ hasText: /\[veo:/ }).first();
      await expect(badge).toBeVisible();
      const cls = await badge.getAttribute('class') ?? '';
      expect(cls).toContain('purple');
    });

    test('C7: [title:...] badge with teal styling', async ({ page }) => {
      await navigateWithMockedSpecs(page, badgeSections);
      const badge = page.locator('span').filter({ hasText: /\[title:/ }).first();
      await expect(badge).toBeVisible();
      const cls = await badge.getAttribute('class') ?? '';
      expect(cls).toContain('teal');
    });

    test('C8: [split:...] badge with orange styling', async ({ page }) => {
      await navigateWithMockedSpecs(page, badgeSections);
      const badge = page.locator('span').filter({ hasText: /\[split:/ }).first();
      await expect(badge).toBeVisible();
      const cls = await badge.getAttribute('class') ?? '';
      expect(cls).toContain('orange');
    });

    test('C9: No firstLine → "—" dash placeholder', async ({ page }) => {
      await navigateWithMockedSpecs(page, badgeSections);
      // The plain.md file has no firstLine → should show "—"
      const dashSpan = page.locator('span.text-slate-400', { hasText: '—' });
      await expect(dashSpan.first()).toBeVisible();
    });

    test('C10: screenshot — table with mixed badges', async ({ page }) => {
      await navigateWithMockedSpecs(page, badgeSections);
      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-C10-badges.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group D: Generate & Regenerate (8 tests)
  // =========================================================================
  test.describe('Group D: Generate & regenerate', () => {
    test('D1: "Generate All Specs" fires POST /api/pipeline/specs/run with empty {}', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      let requestBody: unknown = null;
      await page.route('**/api/pipeline/specs/run', (route) => {
        requestBody = route.request().postDataJSON();
        const sseBody = 'data: {"type":"complete","jobId":"test-d1"}\n\n';
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: sseBody,
        });
      });

      await page.locator('button', { hasText: 'Generate All Specs' }).click();
      await page.waitForTimeout(500);
      expect(requestBody).toEqual({});
    });

    test('D2: Section "↺ Regenerate" fires POST with { sections: [sectionId] }', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      let requestBody: any = null;
      await page.route('**/api/pipeline/specs/run', (route) => {
        requestBody = route.request().postDataJSON();
        const sseBody = 'data: {"type":"complete","jobId":"test-d2"}\n\n';
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: sseBody,
        });
      });

      const sectionRegen = page.locator('button', { hasText: '↺ Regenerate' }).first();
      await sectionRegen.click();
      await page.waitForTimeout(500);

      expect(requestBody).toHaveProperty('sections');
      expect(requestBody.sections).toHaveLength(1);
      expect(requestBody.sections[0]).toBe('cold-open');
    });

    test('D3: File "↺" button fires POST with { files: [filePath] }', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      let requestBody: any = null;
      await page.route('**/api/pipeline/specs/run', (route) => {
        requestBody = route.request().postDataJSON();
        const sseBody = 'data: {"type":"complete","jobId":"test-d3"}\n\n';
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: sseBody,
        });
      });

      const fileRegen = page.locator('button[title="Regenerate file"]').first();
      await fileRegen.click();
      await page.waitForTimeout(500);

      expect(requestBody).toHaveProperty('files');
      expect(requestBody.files).toHaveLength(1);
      expect(requestBody.files[0]).toBe('specs/00-cold-open/spec.md');
    });

    test('D4: SSE response with jobId → SseLogPanel activates', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      const TEST_JOB_ID = 'test-d4-job';

      await page.route('**/api/pipeline/specs/run', (route) => {
        const sseBody = [
          'data: {"type":"log","message":"Generating specs..."}\n\n',
          `data: {"type":"complete","jobId":"${TEST_JOB_ID}"}\n\n`,
        ].join('');
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: sseBody,
        });
      });

      let jobStreamRequested = false;
      await page.route(`**/api/jobs/${TEST_JOB_ID}/stream`, (route) => {
        jobStreamRequested = true;
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: '',
        });
      });

      await page.locator('button', { hasText: 'Generate All Specs' }).click();
      await page.waitForTimeout(2000);

      expect(jobStreamRequested).toBe(true);
    });

    test('D5: SSE error event sets error state', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      await page.route('**/api/pipeline/specs/run', (route) => {
        const sseBody = 'event: error\ndata: {"message":"Spec generation failed"}\n\n';
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: sseBody,
        });
      });

      await page.locator('button', { hasText: 'Generate All Specs' }).click();
      await page.waitForTimeout(1000);

      await expect(page.locator('text=Error:').first()).toBeVisible({ timeout: 3000 });
    });

    test('D6: POST network failure does not crash component', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      await page.route('**/api/pipeline/specs/run', (route) => {
        return route.abort('connectionrefused');
      });

      await page.locator('button', { hasText: 'Generate All Specs' }).click();
      await page.waitForTimeout(500);

      // Component should not crash — heading still visible
      await expect(page.locator('h2', { hasText: 'Stage 6' })).toBeVisible();
    });

    test('D7: Logs drawer <details> can be opened to see SseLogPanel', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      // Scroll to logs
      await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
      await page.waitForTimeout(300);

      const summary = page.locator('summary', { hasText: 'Spec Generation Logs' });
      await summary.click();
      await page.waitForTimeout(300);

      // The details should now be open
      const detailsEl = page.locator('details', { has: summary });
      const isOpen = await detailsEl.getAttribute('open');
      expect(isOpen).not.toBeNull();
    });

    test('D8: screenshot — SSE logs visible in drawer', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      const TEST_JOB_ID = 'test-d8-job';

      await page.route('**/api/pipeline/specs/run', (route) => {
        const sseBody = `data: {"type":"complete","jobId":"${TEST_JOB_ID}"}\n\n`;
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: sseBody,
        });
      });

      await page.route(`**/api/jobs/${TEST_JOB_ID}/stream`, (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"message":"Starting generation..."}\n\ndata: {"message":"Processing section 1..."}\n\n',
        });
      });

      await page.locator('button', { hasText: 'Generate All Specs' }).click();
      await page.waitForTimeout(1500);

      // Open logs drawer
      await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
      await page.waitForTimeout(300);
      await page.locator('summary', { hasText: 'Spec Generation Logs' }).click();
      await page.waitForTimeout(500);

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-D8-sse-logs.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group E: Inline Editor (9 tests)
  // =========================================================================
  test.describe('Group E: Inline editor', () => {
    test('E1: Clicking ✎ edit button opens editor in correct section', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      await expect(page.locator('text=Editing:').first()).toBeVisible();
    });

    test('E2: "Editing: {path}" title displayed', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      await expect(page.locator('text=Editing: specs/00-cold-open/spec.md')).toBeVisible();
    });

    test('E3: CodeMirror .cm-editor container visible with height 240px', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await expect(cmEditor).toBeVisible();

      // Check height attribute on the CodeMirror wrapper
      const height = await cmEditor.evaluate((el) => {
        return getComputedStyle(el).height;
      });
      expect(parseInt(height)).toBeGreaterThanOrEqual(240);
    });

    test('E4: Editor loads file content from GET /api/pipeline/specs/file', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS, {
        'specs/00-cold-open/spec.md': '# Cold Open Spec\n\nThis is a test.',
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      // Verify content is loaded in the editor
      const cmContent = page.locator('.cm-content');
      await expect(cmContent).toBeVisible();
      const text = await cmContent.textContent();
      expect(text).toContain('Cold Open Spec');
    });

    test('E5: "Loading file…" shown during slow file fetch', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      // Override file route with slow response
      await page.route('**/api/pipeline/specs/file**', async (route) => {
        if (route.request().method() === 'GET') {
          await new Promise((resolve) => setTimeout(resolve, 2000));
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ content: '# Content' }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();

      await expect(page.locator('text=Loading file…')).toBeVisible({ timeout: 2000 });
    });

    test('E6: Editor error content when file load fails (500)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      // Override file route with error
      await page.route('**/api/pipeline/specs/file**', (route) => {
        if (route.request().method() === 'GET') {
          return route.fulfill({
            status: 500,
            contentType: 'application/json',
            body: JSON.stringify({ error: 'Internal Server Error' }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      // Editor should contain error message
      const cmContent = page.locator('.cm-content');
      await expect(cmContent).toBeVisible();
      const text = await cmContent.textContent();
      expect(text).toContain('Error loading file');
    });

    test('E7: Typing in editor updates content', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type('New content added');
      await page.waitForTimeout(300);

      const cmContent = page.locator('.cm-content');
      const text = await cmContent.textContent();
      expect(text).toContain('New content added');
    });

    test('E8: "Saving…" indicator visible during auto-save PUT', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      // Slow PUT response
      await page.route('**/api/pipeline/specs/file', async (route) => {
        if (route.request().method() === 'PUT') {
          await new Promise((resolve) => setTimeout(resolve, 800));
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ ok: true }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type(' change');

      // Trigger blur
      await page.locator('h2').first().click();

      // Wait for 1s debounce to fire
      await page.waitForTimeout(1200);
      await expect(page.locator('text=Saving…')).toBeVisible({ timeout: 500 });

      // After save completes, indicator disappears
      await expect(page.locator('text=Saving…')).not.toBeVisible({ timeout: 3000 });
    });

    test('E9: screenshot — editor open with content', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS, {
        'specs/00-cold-open/spec.md': '# Cold Open Spec\n\nThis section introduces the video topic.\n\n## Scene 1\nTitle card with animated text.',
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-E9-editor.png'),
        fullPage: true,
      });
    });

    test('E10: Script Context panel shows aligned narration beside the spec editor', async ({ page }) => {
      await navigateWithMockedSpecs(
        page,
        [
          {
            id: 'cold_open',
            label: 'Cold Open',
            files: [
              { path: 'specs/00-cold-open/spec.md', exists: true, firstLine: '[Remotion] Title Card' },
            ],
          },
        ],
        {
          'specs/00-cold-open/spec.md': [
            '# Section 1.1: Cold Open',
            '',
            '## Narration Sync',
            '> "A clean narration line for the cold open."',
            '',
            '## Code Structure (Remotion)',
            '```typescript',
            '<Sequence />',
            '```',
          ].join('\n'),
        },
        [
          '# Mock Script',
          '',
          '## COLD OPEN',
          '',
          '**[VISUAL: [Remotion] Title text lands in the center.]**',
          '',
          '**NARRATOR:**',
          'A clean narration line for the cold open.',
        ].join('\n'),
      );

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      await expect(page.locator('text=Script Context')).toBeVisible();
      await expect(page.locator('text=COLD OPEN')).toBeVisible();
      await expect(page.locator('text=A clean narration line for the cold open.')).toHaveCount(2);
    });
  });

  // =========================================================================
  // Group F: Auto-Save & File Operations (7 tests)
  // =========================================================================
  test.describe('Group F: Auto-save & file operations', () => {
    test('F1: Editor blur triggers auto-save after 1s debounce', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      let putCalled = false;
      await page.route('**/api/pipeline/specs/file', (route) => {
        if (route.request().method() === 'PUT') {
          putCalled = true;
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ ok: true }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type(' Modified');

      // Trigger blur
      await page.locator('h2').first().click();

      // Before debounce fires
      await page.waitForTimeout(500);
      expect(putCalled).toBe(false);

      // After debounce fires (1s) + network time
      await page.waitForTimeout(1000);
      expect(putCalled).toBe(true);
    });

    test('F2: PUT body includes { path, content } with updated content', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      let putBody: any = null;
      await page.route('**/api/pipeline/specs/file', (route) => {
        if (route.request().method() === 'PUT') {
          putBody = route.request().postDataJSON();
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ ok: true }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type(' Modified');

      // Trigger blur + wait for debounce
      await page.locator('h2').first().click();
      await page.waitForTimeout(1500);

      expect(putBody).toBeTruthy();
      expect(putBody.path).toBe('specs/00-cold-open/spec.md');
      expect(putBody.content).toContain('Modified');
    });

    test('F3: Save failure (500) does not crash — finally block clears saving', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      await page.route('**/api/pipeline/specs/file', (route) => {
        if (route.request().method() === 'PUT') {
          return route.fulfill({
            status: 500,
            contentType: 'application/json',
            body: JSON.stringify({ error: 'Server error' }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type(' change');
      await page.locator('h2').first().click();
      await page.waitForTimeout(2000);

      // Component should not crash
      await expect(page.locator('h2', { hasText: 'Stage 6' })).toBeVisible();
      // "Saving…" should have cleared
      await expect(page.locator('text=Saving…')).not.toBeVisible();
    });

    test('F4: Rapid typing + blur only triggers one save (debounce)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      let putCount = 0;
      await page.route('**/api/pipeline/specs/file', (route) => {
        if (route.request().method() === 'PUT') {
          putCount++;
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ ok: true }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();

      // Rapid typing
      await page.keyboard.type('a');
      await page.keyboard.type('b');
      await page.keyboard.type('c');

      // Single blur
      await page.locator('h2').first().click();
      await page.waitForTimeout(2000);

      // Should have triggered only 1 save
      expect(putCount).toBe(1);
    });

    test('F5: CodeMirror text is readable (contrast check — not white-on-white)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS, {
        'specs/00-cold-open/spec.md': '# Visible Content\nThis text should be readable.',
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await expect(cmEditor).toBeVisible();

      const { editorBg, textColor } = await cmEditor.evaluate((el) => {
        const editorStyle = getComputedStyle(el);
        const content = el.querySelector('.cm-content');
        const contentStyle = content ? getComputedStyle(content) : null;
        return {
          editorBg: editorStyle.backgroundColor,
          textColor: contentStyle ? contentStyle.color : editorStyle.color,
        };
      });

      const parseRgb = (css: string) => {
        const m = css.match(/\d+/g);
        return m ? [Number(m[0]), Number(m[1]), Number(m[2])] : [0, 0, 0];
      };
      const [tr, tg, tb] = parseRgb(textColor);
      const [br, bg2, bb] = parseRgb(editorBg);

      const diff = Math.abs(tr - br) + Math.abs(tg - bg2) + Math.abs(tb - bb);
      expect(diff).toBeGreaterThan(100);
    });

    test('F6: "Saving…" appears during PUT and disappears after', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      await page.route('**/api/pipeline/specs/file', async (route) => {
        if (route.request().method() === 'PUT') {
          await new Promise((resolve) => setTimeout(resolve, 600));
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ ok: true }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type(' change');
      await page.locator('h2').first().click();

      // Wait for debounce
      await page.waitForTimeout(1200);
      await expect(page.locator('text=Saving…')).toBeVisible({ timeout: 500 });
      await expect(page.locator('text=Saving…')).not.toBeVisible({ timeout: 3000 });
    });

    test('F7: screenshot — saving indicator', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);

      await page.route('**/api/pipeline/specs/file', async (route) => {
        if (route.request().method() === 'PUT') {
          await new Promise((resolve) => setTimeout(resolve, 2000));
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ ok: true }),
          });
        }
        return route.fallback();
      });

      const editBtn = page.locator('button[title="Open in editor"]').first();
      await editBtn.click();
      await page.waitForTimeout(500);

      const cmEditor = page.locator('.cm-editor').first();
      await cmEditor.click();
      await page.keyboard.type(' saving test');
      await page.locator('h2').first().click();
      await page.waitForTimeout(1200);

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-F7-saving.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group G: Edge Cases & Navigation (8 tests)
  // =========================================================================
  test.describe('Group G: Edge cases & navigation', () => {
    test('G1: Continue button always enabled (no allDone gate)', async ({ page }) => {
      await navigateWithMockedSpecs(page, DEFAULT_SECTIONS);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      await expect(btn).toBeEnabled();
    });

    test('G2: Continue click navigates to Stage 7 (Veo Gen heading visible)', async ({ page }) => {
      await navigateToStage6(page);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      await btn.click();
      await page.waitForTimeout(1000);

      await expect(page.locator('text=Veo').first()).toBeVisible();
    });

    test('G3: Network error on /api/pipeline/specs/list → error message in red', async ({ page }) => {
      await page.route('**/api/pipeline/specs/list', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      });

      await navigateToStage6(page);
      await page.waitForTimeout(1500);

      const errorMsg = page.locator('.text-red-500', { hasText: 'Error:' });
      await expect(errorMsg).toBeVisible({ timeout: 5000 });
    });

    test('G4: Error state shows "Error: {message}" with text-red-500', async ({ page }) => {
      await page.route('**/api/pipeline/specs/list', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Server error' }),
        });
      });

      await navigateToStage6(page);
      await page.waitForTimeout(1500);

      const errorDiv = page.locator('div.text-red-500');
      await expect(errorDiv).toBeVisible();
      const text = await errorDiv.textContent();
      expect(text).toContain('Error:');
    });

    test('G5: Component recovers — heading still visible after error', async ({ page }) => {
      await page.route('**/api/pipeline/specs/list', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Server error' }),
        });
      });

      await navigateToStage6(page);
      await page.waitForTimeout(1500);

      // Heading still visible even after error
      await expect(page.locator('h2', { hasText: 'Stage 6' })).toBeVisible();
      // Generate button still visible
      await expect(page.locator('button', { hasText: 'Generate All Specs' })).toBeVisible();
    });

    test('G6: Section with 0 files renders accordion but empty table body', async ({ page }) => {
      await navigateWithMockedSpecs(page, [
        { id: 'empty-section', label: 'Empty Section', files: [] },
      ]);

      // Section label should be visible
      await expect(page.locator('button', { hasText: 'Empty Section' })).toBeVisible();

      // Table headers should render
      await expect(page.locator('th', { hasText: 'Type' }).first()).toBeVisible();

      // But no file rows
      const fileRows = page.locator('tbody tr');
      const count = await fileRows.count();
      expect(count).toBe(0);
    });

    test('G7: Multiple sections with mixed file counts', async ({ page }) => {
      await navigateWithMockedSpecs(page, [
        {
          id: 'section-a',
          label: 'Section A (2 files)',
          files: [
            { path: 'specs/a/one.md', exists: true, firstLine: '[Remotion] Card' },
            { path: 'specs/a/two.md', exists: false },
          ],
        },
        {
          id: 'section-b',
          label: 'Section B (1 file)',
          files: [{ path: 'specs/b/only.md', exists: true, firstLine: '[veo:pan] scene' }],
        },
        {
          id: 'section-c',
          label: 'Section C (0 files)',
          files: [],
        },
      ]);

      await expect(page.locator('button', { hasText: 'Section A (2 files)' })).toBeVisible();
      await expect(page.locator('button', { hasText: 'Section B (1 file)' })).toBeVisible();
      await expect(page.locator('button', { hasText: 'Section C (0 files)' })).toBeVisible();

      // Verify file paths from sections with files
      await expect(page.locator('text=specs/a/one.md')).toBeVisible();
      await expect(page.locator('text=specs/b/only.md')).toBeVisible();
    });

    test('G8: screenshot — error state', async ({ page }) => {
      await page.route('**/api/pipeline/specs/list', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      });

      await navigateToStage6(page);
      await page.waitForTimeout(1500);

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage6-G8-error-state.png'),
        fullPage: true,
      });
    });
  });
});
