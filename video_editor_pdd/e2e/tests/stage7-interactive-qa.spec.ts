import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

function stage7SectionSelect(page: import('@playwright/test').Page) {
  return page.getByLabel('Section');
}

/**
 * Navigate to Stage 7 (Veo Generation) via the sidebar.
 */
async function navigateToStage7(page: import('@playwright/test').Page) {
  await page.goto('/');
  await page.waitForLoadState('networkidle');

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });

  // Wait for React hydration
  await page.waitForTimeout(1000);

  const heading = page.locator('h2', { hasText: 'Stage 7' });

  await sidebar.locator('button', { hasText: 'Veo Gen' }).first().click();
  await expect(heading).toBeVisible({ timeout: 10000 });

  await page.waitForTimeout(500);
}

/**
 * Navigate to Stage 7 with mocked GET /api/pipeline/veo/clips and SSE stream.
 * Sets up route mocks BEFORE navigating so they're in place for the fetch.
 */
async function navigateWithMockedClips(
  page: import('@playwright/test').Page,
  clips: Array<{
    id: string;
    sectionId: string;
    aspectRatio: string;
    status: string;
    specPath?: string | null;
    stale?: boolean;
    frameChainDeps?: string[];
  }>,
  references: Array<{ id: string; label?: string }> = [],
  specFileContent: Record<string, string> = {},
) {
  await page.route('**/api/pipeline/veo/clips', (route) => {
    return route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ clips, references }),
    });
  });

  // Mock SSE stream to prevent hanging EventSource
  await page.route('**/api/pipeline/veo/stream', (route) => {
    return route.fulfill({
      status: 200,
      headers: { 'Content-Type': 'text/event-stream' },
      body: 'data: {"type":"connected"}\n\n',
    });
  });

  // Mock reference portrait images - serve a 1x1 transparent PNG
  await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
    return route.fulfill({
      status: 200,
      contentType: 'image/png',
      // 1x1 transparent PNG
      body: Buffer.from(
        'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
        'base64',
      ),
    });
  });

  await page.route('**/api/pipeline/specs/file**', (route) => {
    const url = new URL(route.request().url());
    const specPath = url.searchParams.get('path') ?? '';
    return route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({
        content:
          specFileContent[specPath] ??
          '# Veo Spec\n\n[veo: A cinematic ocean wave at sunset]\n\n## Visual Description\nGolden-hour ocean footage.',
      }),
    });
  });

  await page.route('**/api/video/outputs/veo/*.mp4', (route) => {
    return route.fulfill({
      status: 200,
      contentType: 'video/mp4',
      body: '',
    });
  });

  await navigateToStage7(page);
  await page.waitForTimeout(500);
}

const MOCK_CLIPS = [
  {
    id: 'cold_open',
    sectionId: 'cold_open',
    aspectRatio: '16:9',
    status: 'missing',
    specPath: 'specs/cold_open/02_ocean.md',
    stale: false,
    frameChainDeps: [],
  },
  {
    id: 'part1_economics',
    sectionId: 'part1_economics',
    aspectRatio: '16:9',
    status: 'done',
    specPath: 'specs/part1_economics/02_ocean.md',
    stale: false,
    frameChainDeps: ['cold_open'],
  },
  {
    id: 'part2_history',
    sectionId: 'part2_history',
    aspectRatio: '16:9',
    status: 'generating',
    specPath: 'specs/part2_history/02_ocean.md',
    stale: false,
    frameChainDeps: ['part1_economics'],
  },
  {
    id: 'part3_future',
    sectionId: 'part3_future',
    aspectRatio: '9:16',
    status: 'error',
    specPath: 'specs/part3_future/02_ocean.md',
    stale: true,
    frameChainDeps: ['part2_history'],
  },
];

const MOCK_REFERENCES = [
  { id: 'alex', label: 'Alex (protagonist)' },
  { id: 'jordan', label: 'Jordan (narrator)' },
];

test.describe('Stage 7: Interactive QA - Comprehensive Feature Testing', () => {
  // =========================================================================
  // Group A: Initial Load & UI Elements (9 tests)
  // =========================================================================
  test.describe('Group A: Initial load & UI elements', () => {
    test('A1: "Stage 7 — Veo Generation" heading visible', async ({ page }) => {
      await navigateToStage7(page);
      const heading = page.locator('h2', { hasText: 'Stage 7' });
      await expect(heading).toBeVisible();
      await expect(heading).toHaveText(/Stage 7 — Veo Generation/);
    });

    test('A2: "Generate All" button visible with bg-blue-600', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const btn = page.locator('button', { hasText: 'Generate All' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-blue-600');
    });

    test('A3: "Generate Missing" button visible with bg-slate-600', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const btn = page.locator('button', { hasText: 'Generate Missing' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-slate-600');
    });

    test('A4: "Generate Section" button visible with bg-indigo-600', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const btn = page.locator('button', { hasText: 'Generate Section' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-indigo-600');
    });

    test('A5: Section dropdown visible with bg-slate-800', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const select = stage7SectionSelect(page);
      await expect(select).toBeVisible();
      const cls = await select.getAttribute('class') ?? '';
      expect(cls).toContain('bg-slate-800');
    });

    test('A6: "Continue →" button visible with bg-emerald-600', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-emerald-600');
    });

    test('A7: Selected clip shows Veo spec beside generated video preview', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES, {
        'specs/cold_open/02_ocean.md': [
          '[veo: A cinematic ocean wave at sunset]',
          '',
          '# Ocean Wave Sunset',
          '',
          '## Visual Description',
          'A calm ocean wave rolling onto a beach at golden hour.',
        ].join('\n'),
        'specs/part1_economics/02_ocean.md': [
          '[veo: A cinematic ocean wave at sunset]',
          '',
          '# Ocean Wave Sunset',
          '',
          '## Visual Description',
          'A calm ocean wave rolling onto a beach at golden hour.',
        ].join('\n'),
      });

      await page.locator('tr', { hasText: 'part1_economics' }).click();

      await expect(page.getByText('Veo Spec', { exact: true })).toBeVisible();
      await expect(page.getByText('Generated Video', { exact: true })).toBeVisible();
      await expect(page.getByText('specs/part1_economics/02_ocean.md', { exact: true })).toBeVisible();
      await expect(page.getByText('part1_economics · 16:9', { exact: true })).toBeVisible();

      const video = page.locator('video');
      if (await video.count()) {
        await expect(video).toBeVisible();
      } else {
        await expect(
          page.getByText('The generated Veo video could not be loaded from disk.', { exact: true })
        ).toBeVisible();
      }
    });

    test('A8: Auto-composite checkbox and label visible', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const label = page.locator('text=Auto-composite split-screen');
      await expect(label).toBeVisible();
      const checkbox = page.locator('input[type="checkbox"]');
      await expect(checkbox).toBeVisible();
      await expect(checkbox).not.toBeChecked();
    });

    test('A9: Loading state shows "Loading Veo clips…"', async ({ page }) => {
      // Delay the clips response so loading state is visible
      await page.route('**/api/pipeline/veo/clips', async (route) => {
        await new Promise((r) => setTimeout(r, 3000));
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });

      await navigateToStage7(page);
      // Should see loading text before clips arrive
      const loadingText = page.locator('text=Loading Veo clips');
      await expect(loadingText).toBeVisible({ timeout: 5000 });
      // Heading should still be visible during loading
      await expect(page.locator('h2', { hasText: 'Stage 7' })).toBeVisible();
    });

    test('A9: Screenshot — full initial state with mocked clips', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-A9-initial-state.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group B: Character References (8 tests)
  // =========================================================================
  test.describe('Group B: Character References', () => {
    test('B1: "Character References" h3 heading visible', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const heading = page.locator('h3', { hasText: 'Character References' });
      await expect(heading).toBeVisible();
    });

    test('B2: Reference label displayed in text-slate-300', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const label = page.locator('text=Alex (protagonist)');
      await expect(label).toBeVisible();
      const cls = await label.evaluate((el) => el.className);
      expect(cls).toContain('text-slate-300');
    });

    test('B3: Portrait image renders for valid reference', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      // With our mocked PNG images, the img should render (not fallback)
      const img = page.locator('img[alt="Alex (protagonist)"]');
      await expect(img).toBeVisible({ timeout: 5000 });
    });

    test('B4: Fallback "No image" shows when portrait fails to load', async ({ page }) => {
      // Override to 404 the portrait images
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({ status: 404 });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1000);

      const fallback = page.locator('[data-testid="ref-portrait-fallback"]').first();
      await expect(fallback).toBeVisible({ timeout: 5000 });
      await expect(fallback).toContainText('No image');
    });

    test('B5: "↺ Regenerate" button visible per reference', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      // Character reference section has Regenerate buttons (left column)
      const refPanel = page.locator('h3', { hasText: 'Character References' }).locator('..');
      const regenBtns = refPanel.locator('button', { hasText: '↺ Regenerate' });
      await expect(regenBtns).toHaveCount(2); // alex + jordan
    });

    test('B6: Regenerate fires POST /api/pipeline/veo/references/run', async ({ page }) => {
      let postBody: any = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/references/run', (route) => {
        postBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-ref-regen-job' }),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Click first Regenerate in the character references panel
      const refPanel = page.locator('h3', { hasText: 'Character References' }).locator('..');
      const firstRegen = refPanel.locator('button', { hasText: '↺ Regenerate' }).first();
      await firstRegen.click();
      await page.waitForTimeout(500);

      expect(postBody).not.toBeNull();
      expect(postBody).toHaveProperty('referenceId', 'alex');
    });

    test('B7: Empty references shows "No reference portraits found."', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, []);
      const emptyMsg = page.locator('text=No reference portraits found.');
      await expect(emptyMsg).toBeVisible();
    });

    test('B8: Screenshot — character references panel', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const refPanel = page.locator('h3', { hasText: 'Character References' }).locator('..');
      await refPanel.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-B8-character-refs.png') });
    });
  });

  // =========================================================================
  // Group C: Frame Chaining (7 tests)
  // =========================================================================
  test.describe('Group C: Frame Chaining', () => {
    test('C1: "Frame Chaining" h3 heading visible', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const heading = page.locator('h3', { hasText: 'Frame Chaining' });
      await expect(heading).toBeVisible();
    });

    test('C2: Section IDs displayed as headings in text-slate-300', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const chainPanel = page.locator('h3', { hasText: 'Frame Chaining' }).locator('..');
      // Each section ID should appear as a div with font-medium text-slate-300
      const sectionHeading = chainPanel.locator('div.font-medium.text-slate-300').first();
      await expect(sectionHeading).toBeVisible();
      await expect(sectionHeading).toContainText('cold_open');
    });

    test('C3: Dependency chain shows "dep → clipId" format', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const chainPanel = page.locator('h3', { hasText: 'Frame Chaining' }).locator('..');
      // part1_economics has deps ['cold_open'], so chain = "cold_open → part1_economics"
      await expect(chainPanel.locator('text=cold_open → part1_economics')).toBeVisible();
    });

    test('C4: No raw file paths in chain display', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const chainPanel = page.locator('h3', { hasText: 'Frame Chaining' }).locator('..');
      // Must NOT contain raw file paths
      await expect(chainPanel.locator('text=outputs/veo')).toHaveCount(0);
      const pngCount = await chainPanel.locator('text=.png').count();
      expect(pngCount).toBe(0);
    });

    test('C5: Clip with no deps shows just clip ID', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const chainPanel = page.locator('h3', { hasText: 'Frame Chaining' }).locator('..');
      // cold_open has no deps, so it should appear as just "cold_open" (no arrow)
      // The section heading is "cold_open" and below it the chain entry is also "cold_open"
      const chainText = chainPanel.locator('div.text-xs.text-slate-400');
      const firstChainEntry = chainText.first().locator('div').first();
      await expect(firstChainEntry).toHaveText('cold_open');
    });

    test('C6: Multiple sections show their own chains', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const chainPanel = page.locator('h3', { hasText: 'Frame Chaining' }).locator('..');
      const sectionHeadings = chainPanel.locator('div.font-medium.text-slate-300');
      const count = await sectionHeadings.count();
      // We have 4 clips across 4 sections
      expect(count).toBe(4);
    });

    test('C7: Screenshot — frame chaining panel', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const chainPanel = page.locator('h3', { hasText: 'Frame Chaining' }).locator('..').locator('..');
      await chainPanel.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-C7-frame-chaining.png') });
    });
  });

  // =========================================================================
  // Group D: Clip Table & Status Badges (9 tests)
  // =========================================================================
  test.describe('Group D: Clip Table & Status Badges', () => {
    test('D1: Table headers visible: Clip, Section, Aspect, Status, Actions', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Section' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Aspect' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Status' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Actions' }).first()).toBeVisible();
    });

    test('D2: Clip ID in font-medium text-slate-200', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const firstCell = page.locator('tbody tr').first().locator('td').first();
      await expect(firstCell).toBeVisible();
      const cls = await firstCell.getAttribute('class') ?? '';
      expect(cls).toContain('font-medium');
      expect(cls).toContain('text-slate-200');
      await expect(firstCell).toContainText('cold_open');
    });

    test('D3: Section ID in text-slate-300', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const sectionCell = page.locator('tbody tr').first().locator('td').nth(1);
      await expect(sectionCell).toBeVisible();
      const cls = await sectionCell.getAttribute('class') ?? '';
      expect(cls).toContain('text-slate-300');
    });

    test('D4: Aspect ratio displayed in text-slate-300', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const aspectCell = page.locator('tbody tr').first().locator('td').nth(2);
      await expect(aspectCell).toBeVisible();
      await expect(aspectCell).toHaveText('16:9');
      const cls = await aspectCell.getAttribute('class') ?? '';
      expect(cls).toContain('text-slate-300');
    });

    test('D5: Status badge colors — done (green), generating (amber), missing (slate), error (red)', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);

      // missing (cold_open) — text-slate-400
      const missingBadge = page.locator('tbody tr').nth(0).locator('span', { hasText: 'missing' });
      await expect(missingBadge).toBeVisible();
      const missingCls = await missingBadge.getAttribute('class') ?? '';
      expect(missingCls).toContain('text-slate-400');

      // done (part1_economics) — text-green-500
      const doneBadge = page.locator('tbody tr').nth(1).locator('span', { hasText: 'done' });
      await expect(doneBadge).toBeVisible();
      const doneCls = await doneBadge.getAttribute('class') ?? '';
      expect(doneCls).toContain('text-green-500');

      // generating (part2_history) — text-amber-500
      const genBadge = page.locator('tbody tr').nth(2).locator('span', { hasText: 'generating' });
      await expect(genBadge).toBeVisible();
      const genCls = await genBadge.getAttribute('class') ?? '';
      expect(genCls).toContain('text-amber-500');

      // error (part3_future) — text-red-500
      const errorBadge = page.locator('tbody tr').nth(3).locator('span', { hasText: 'error' });
      await expect(errorBadge).toBeVisible();
      const errorCls = await errorBadge.getAttribute('class') ?? '';
      expect(errorCls).toContain('text-red-500');
    });

    test('D6: Generating badge has animate-pulse', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const genBadge = page.locator('tbody tr').nth(2).locator('span', { hasText: 'generating' });
      await expect(genBadge).toBeVisible();
      const cls = await genBadge.getAttribute('class') ?? '';
      expect(cls).toContain('animate-pulse');
    });

    test('D7: Stale indicator ⚠ in text-amber-500 for stale clips', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      // part3_future is stale=true
      const staleRow = page.locator('tbody tr').nth(3);
      const staleIndicator = staleRow.locator('span', { hasText: '⚠' });
      await expect(staleIndicator).toBeVisible();
      const cls = await staleIndicator.getAttribute('class') ?? '';
      expect(cls).toContain('text-amber-500');
    });

    test('D8: Per-clip "↺ Regenerate" button in each table row', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const rows = page.locator('tbody tr');
      const rowCount = await rows.count();
      expect(rowCount).toBe(4);
      for (let i = 0; i < rowCount; i++) {
        const btn = rows.nth(i).locator('button', { hasText: '↺ Regenerate' });
        await expect(btn).toBeVisible();
      }
    });

    test('D9: Screenshot — clip table with mixed statuses', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const table = page.locator('table').first();
      await table.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-D9-clip-table.png') });
    });
  });

  // =========================================================================
  // Group E: Generate Actions (9 tests)
  // =========================================================================
  test.describe('Group E: Generate Actions', () => {
    test('E1: "Generate All" fires POST with ALL clip IDs + autoComposite', async ({ page }) => {
      let postBody: any = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        postBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-all-job' }),
        });
      });
      // Mock job stream for SseLogPanel
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"message":"Starting generation..."}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      await page.locator('button', { hasText: 'Generate All' }).click();
      await page.waitForTimeout(500);

      expect(postBody).not.toBeNull();
      expect(postBody.clips).toEqual(['cold_open', 'part1_economics', 'part2_history', 'part3_future']);
      expect(postBody.autoComposite).toBe(false);
    });

    test('E2: "Generate Missing" fires POST with only missing clip IDs', async ({ page }) => {
      let postBody: any = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        postBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-missing-job' }),
        });
      });
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"message":"Starting generation..."}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      await page.locator('button', { hasText: 'Generate Missing' }).click();
      await page.waitForTimeout(500);

      expect(postBody).not.toBeNull();
      // Only cold_open is 'missing'
      expect(postBody.clips).toEqual(['cold_open']);
    });

    test('E3: "Generate Section" fires POST with only clips matching selectedSection', async ({ page }) => {
      let postBody: any = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        postBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-section-job' }),
        });
      });
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"message":"Starting generation..."}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Select part2_history section
      const select = stage7SectionSelect(page);
      await select.selectOption('part2_history');
      await page.waitForTimeout(300);

      await page.locator('button', { hasText: 'Generate Section' }).click();
      await page.waitForTimeout(500);

      expect(postBody).not.toBeNull();
      expect(postBody.clips).toEqual(['part2_history']);
    });

    test('E4: Per-clip "↺ Regenerate" fires POST with single clip ID', async ({ page }) => {
      let postBody: any = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        postBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-single-job' }),
        });
      });
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"message":"Starting generation..."}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Click the Regenerate button in the second row (part1_economics)
      const secondRowBtn = page.locator('tbody tr').nth(1).locator('button', { hasText: '↺ Regenerate' });
      await secondRowBtn.click();
      await page.waitForTimeout(500);

      expect(postBody).not.toBeNull();
      expect(postBody.clips).toEqual(['part1_economics']);
    });

    test('E5: Optimistic update — clips change to generating immediately', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      // Delay the run response so we can observe optimistic update
      await page.route('**/api/pipeline/veo/run', async (route) => {
        await new Promise((r) => setTimeout(r, 2000));
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-optimistic-job' }),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Initially cold_open is 'missing'
      const firstRow = page.locator('tbody tr').nth(0);
      await expect(firstRow.locator('span', { hasText: 'missing' })).toBeVisible();

      // Click Generate All — should immediately show 'generating' optimistically
      await page.locator('button', { hasText: 'Generate All' }).click();

      // All clips should become 'generating' immediately (before POST completes)
      await expect(firstRow.locator('span', { hasText: 'generating' })).toBeVisible({ timeout: 1000 });
    });

    test('E6: POST failure reverts clips to error status', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      // Return 500 to trigger error revert
      await page.route('**/api/pipeline/veo/run', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Server error' }),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Click Generate All — optimistic to 'generating', then reverts to 'error'
      await page.locator('button', { hasText: 'Generate All' }).click();
      await page.waitForTimeout(1000);

      // cold_open was 'missing', should now be 'error' (reverted from 'generating')
      const firstRow = page.locator('tbody tr').nth(0);
      await expect(firstRow.locator('span', { hasText: 'error' })).toBeVisible({ timeout: 3000 });
    });

    test('E7: Network abort does not crash component', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        return route.abort();
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      await page.locator('button', { hasText: 'Generate All' }).click();
      await page.waitForTimeout(1000);

      // Component should still be alive — heading visible
      await expect(page.locator('h2', { hasText: 'Stage 7' })).toBeVisible();
      // Clips should revert to 'error' on abort
      const firstRow = page.locator('tbody tr').nth(0);
      await expect(firstRow.locator('span', { hasText: 'error' })).toBeVisible({ timeout: 3000 });
    });

    test('E8: autoComposite: true sent when checkbox is checked', async ({ page }) => {
      let postBody: any = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        postBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-composite-job' }),
        });
      });
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"message":"Starting generation..."}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Check the auto-composite checkbox
      const checkbox = page.locator('input[type="checkbox"]');
      await checkbox.check();
      await expect(checkbox).toBeChecked();

      await page.locator('button', { hasText: 'Generate All' }).click();
      await page.waitForTimeout(500);

      expect(postBody).not.toBeNull();
      expect(postBody.autoComposite).toBe(true);
    });

    test('E9: Screenshot — generating state (amber pulsing badges)', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      // part2_history starts as 'generating' — capture it
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-E9-generating-state.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group F: SSE & Logs (8 tests)
  // =========================================================================
  test.describe('Group F: SSE & Logs', () => {
    test('F1: SseLogPanel renders when jobId is set after POST', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-veo-log-job' }),
        });
      });
      // Empty stream body so "Waiting for logs…" appears
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: '',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      // Before generation, SseLogPanel should NOT be rendered (jobId is null)
      const ssePanel = page.locator('text=Waiting for logs');
      const initiallyVisible = await ssePanel.isVisible().catch(() => false);
      expect(initiallyVisible).toBe(false);

      // Trigger generation
      await page.locator('button', { hasText: 'Generate All' }).click();
      await page.waitForTimeout(1000);

      // Now SseLogPanel should be visible with "Waiting for logs…"
      await expect(ssePanel).toBeVisible({ timeout: 5000 });
    });

    test('F2: Per-clip SSE events update clip status in table', async ({ page }) => {
      let sseResolve: ((value: void) => void) | null = null;

      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      // For the per-clip SSE stream, send an event that updates cold_open to 'done'
      await page.route('**/api/pipeline/veo/stream', (route) => {
        const body = [
          'data: {"type":"connected"}\n\n',
          'data: {"clipId":"cold_open","status":"done","message":"Clip cold_open completed"}\n\n',
        ].join('');
        return route.fulfill({
          status: 200,
          headers: {
            'Content-Type': 'text/event-stream',
            'Cache-Control': 'no-cache',
          },
          body,
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1500);

      // cold_open should be updated to 'done' by the SSE event
      const firstRow = page.locator('tbody tr').nth(0);
      await expect(firstRow.locator('span', { hasText: 'done' })).toBeVisible({ timeout: 5000 });
    });

    test('F3: Per-clip SSE events appear in Clip Events panel', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        const body = [
          'data: {"type":"connected"}\n\n',
          'data: {"clipId":"cold_open","message":"Rendering frame 1/100","status":"generating"}\n\n',
        ].join('');
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body,
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1500);

      // Look for the message in the Clip Events panel
      const clipEventsPanel = page.locator('[data-testid="clip-events-heading"]').locator('..');
      await expect(clipEventsPanel.locator('text=cold_open')).toBeVisible({ timeout: 5000 });
      await expect(clipEventsPanel.locator('text=Rendering frame 1/100')).toBeVisible();
    });

    test('F4: "Clip Events" h3 heading visible', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const heading = page.locator('[data-testid="clip-events-heading"]');
      await expect(heading).toBeVisible();
      await expect(heading).toHaveText('Clip Events');
    });

    test('F5: Clip events panel has max-h-40 overflow-y-auto', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      // The events container may be empty (zero height) so check it's attached with correct classes
      const eventsContainer = page.locator('[data-testid="clip-events-heading"]').locator('..').locator('div.max-h-40');
      await expect(eventsContainer).toBeAttached();
      const cls = await eventsContainer.getAttribute('class') ?? '';
      expect(cls).toContain('max-h-40');
      expect(cls).toContain('overflow-y-auto');
    });

    test('F6: SseLogPanel shows "Waiting for logs…" initially after generation', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });
      await page.route('**/api/pipeline/veo/run', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-waiting-job' }),
        });
      });
      // Don't send any messages on the job stream — keep empty
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: '',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(500);

      await page.locator('button', { hasText: 'Generate All' }).click();
      await page.waitForTimeout(1000);

      await expect(page.locator('text=Waiting for logs')).toBeVisible({ timeout: 5000 });
    });

    test('F7: SSE connection failure does not crash component', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      // Abort the SSE stream to simulate connection failure
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.abort();
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1000);

      // Component should still render fully despite SSE failure
      await expect(page.locator('h2', { hasText: 'Stage 7' })).toBeVisible();
      await expect(page.locator('button', { hasText: 'Generate All' })).toBeVisible();
    });

    test('F8: Screenshot — clip events panel with log entries', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ clips: MOCK_CLIPS, references: MOCK_REFERENCES }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        const body = [
          'data: {"type":"connected"}\n\n',
          'data: {"clipId":"cold_open","message":"Starting generation","status":"generating"}\n\n',
          'data: {"clipId":"cold_open","message":"Frame 1/100 rendered","status":"generating"}\n\n',
          'data: {"clipId":"part1_economics","message":"Starting generation","status":"generating"}\n\n',
        ].join('');
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body,
        });
      });
      await page.route('**/api/video/outputs/veo/references/*.png', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'image/png',
          body: Buffer.from(
            'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
            'base64',
          ),
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1500);

      const eventsPanel = page.locator('[data-testid="clip-events-heading"]').locator('..');
      await eventsPanel.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-F8-clip-events.png') });
    });
  });

  // =========================================================================
  // Group G: Edge Cases & Navigation (8 tests)
  // =========================================================================
  test.describe('Group G: Edge Cases & Navigation', () => {
    test('G1: Continue button always enabled (no gate)', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      await expect(btn).toBeEnabled();
    });

    test('G2: Continue click navigates to Stage 8 ("Composition" heading visible)', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, MOCK_REFERENCES);
      const btn = page.locator('button', { hasText: 'Continue' });
      await btn.click();
      await page.waitForTimeout(1000);
      await expect(page.locator('text=Composition').first()).toBeVisible({ timeout: 5000 });
    });

    test('G3: Network error on /api/pipeline/veo/clips shows error message in red', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1000);

      const errorDiv = page.locator('.text-red-500', { hasText: 'Error' });
      await expect(errorDiv).toBeVisible({ timeout: 5000 });
    });

    test('G4: Error state shows "Error: {message}" with text-red-500', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Server error' }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1000);

      const errorDiv = page.locator('.text-red-500');
      await expect(errorDiv).toBeVisible({ timeout: 5000 });
      await expect(errorDiv).toContainText('Error:');
      await expect(errorDiv).toContainText('Failed to load clip list');
    });

    test('G5: Heading still visible in error state', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Server error' }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1000);

      await expect(page.locator('h2', { hasText: 'Stage 7 — Veo Generation' })).toBeVisible();
    });

    test('G6: Empty clips array renders empty table body', async ({ page }) => {
      await navigateWithMockedClips(page, [], MOCK_REFERENCES);
      const rows = page.locator('tbody tr');
      await expect(rows).toHaveCount(0);
    });

    test('G7: Empty references array shows "No reference portraits found."', async ({ page }) => {
      await navigateWithMockedClips(page, MOCK_CLIPS, []);
      await expect(page.locator('text=No reference portraits found.')).toBeVisible();
    });

    test('G8: Screenshot — error state', async ({ page }) => {
      await page.route('**/api/pipeline/veo/clips', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Server error' }),
        });
      });
      await page.route('**/api/pipeline/veo/stream', (route) => {
        return route.fulfill({
          status: 200,
          headers: { 'Content-Type': 'text/event-stream' },
          body: 'data: {"type":"connected"}\n\n',
        });
      });

      await navigateToStage7(page);
      await page.waitForTimeout(1000);

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage7-G8-error-state.png'), fullPage: true });
    });
  });
});
