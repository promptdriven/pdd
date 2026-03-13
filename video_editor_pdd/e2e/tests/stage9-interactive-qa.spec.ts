import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

// ── Shared mock data ──────────────────────────────────────────────────────────

const ALL_STATUS_SECTIONS = [
  { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
  { id: 'part1_economics', durationSeconds: 382.18, status: 'rendering', progress: 65 },
  { id: 'part2_paradigm_shift', durationSeconds: 0, status: 'missing', progress: 0 },
  { id: 'part3_mold', durationSeconds: 0, status: 'error', progress: 0 },
];

const FULL_VIDEO_EXISTS = {
  exists: true,
  sizeBytes: 1610612736, // ~1.50 GB
  durationSeconds: 120.50,
};

const FULL_VIDEO_NONE = { exists: false };

// ── Helpers ───────────────────────────────────────────────────────────────────

async function navigateToStage9(page: import('@playwright/test').Page) {
  await page.goto('/', { waitUntil: 'domcontentloaded' });
  await expect(page.locator('button', { hasText: 'Pipeline' })).toBeVisible({
    timeout: 15000,
  });

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });
  await expect(sidebar.locator('button').filter({ hasText: /^9\s*Render/ })).toBeVisible({
    timeout: 10000,
  });

  const heading = page.locator('h2', { hasText: 'Stage 9' });
  const stageButton = sidebar.locator('button').filter({ hasText: /^9\s*Render/ });

  await stageButton.click();
  try {
    await expect(heading).toBeVisible({ timeout: 3000 });
  } catch {
    await page.waitForTimeout(500);
    await page.evaluate(() => {
      const items = Array.from(document.querySelectorAll('aside button'));
      const target = items.find((item) =>
        item.textContent?.trim().match(/^9\s*Render/)
      );
      if (target) (target as HTMLElement).click();
    });
    try {
      await expect(heading).toBeVisible({ timeout: 3000 });
    } catch {
      await page.waitForTimeout(1000);
      await stageButton.click({ force: true });
      await expect(heading).toBeVisible({ timeout: 10000 });
    }
  }

  await page.waitForTimeout(500);
}

async function navigateWithMockedStatus(
  page: import('@playwright/test').Page,
  sections: unknown[],
  fullVideo: unknown,
) {
  await page.route('**/api/pipeline/render/status', (route) =>
    route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ sections, fullVideo }),
    })
  );
  // Mock SSE stream to prevent hanging EventSource
  await page.route('**/api/pipeline/render/stream**', (route) =>
    route.fulfill({
      status: 200,
      headers: { 'Content-Type': 'text/event-stream' },
      body: 'data: {"type":"connected"}\n\n',
    })
  );

  await navigateToStage9(page);
}

// ── Group A: Status Badge Rendering & CSS (8 tests) ──────────────────────────

test.describe('Stage 9 QA · A: Status Badge Rendering & CSS', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
  });

  test('A1: done badge shows "Rendered" with green classes', async ({ page }) => {
    const row = page.locator('tbody tr').nth(0);
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Rendered' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-green-900/50');
    expect(classes).toContain('text-green-300');
  });

  test('A2: rendering badge shows "Rendering" with blue classes', async ({ page }) => {
    const row = page.locator('tbody tr').nth(1);
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Rendering' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-blue-900/50');
    expect(classes).toContain('text-blue-300');
  });

  test('A3: missing badge shows "Missing" with yellow classes', async ({ page }) => {
    const row = page.locator('tbody tr').nth(2);
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Missing' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-yellow-900/50');
    expect(classes).toContain('text-yellow-300');
  });

  test('A4: error badge shows "Error" with red classes', async ({ page }) => {
    const row = page.locator('tbody tr').nth(3);
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Error' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-red-900/50');
    expect(classes).toContain('text-red-300');
  });

  test('A5: all 4 badge types rendered simultaneously', async ({ page }) => {
    for (const label of ['Rendered', 'Rendering', 'Missing', 'Error']) {
      await expect(page.locator('span.rounded-full', { hasText: label }).first()).toBeVisible();
    }
  });

  test('A6: badge has base classes rounded-full px-2 py-1 text-xs font-medium', async ({ page }) => {
    const badge = page.locator('span.rounded-full', { hasText: 'Rendered' }).first();
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('rounded-full');
    expect(classes).toContain('px-2');
    expect(classes).toContain('py-1');
    expect(classes).toContain('text-xs');
    expect(classes).toContain('font-medium');
  });

  test('A7: badges do NOT have border class (pill-shaped, no border)', async ({ page }) => {
    const badge = page.locator('span.rounded-full', { hasText: 'Rendered' }).first();
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    // The component uses no border class on status badges
    expect(classes).not.toMatch(/\bborder\b/);
  });

  test('A8: screenshot — all four status badges', async ({ page }) => {
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-A8-status-badges.png'),
      fullPage: true,
    });
  });
});

// ── Group B: Section Table Data & Progress Bars (8 tests) ────────────────────

test.describe('Stage 9 QA · B: Section Table Data & Progress Bars', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
  });

  test('B1: section ID displayed in font-mono text-slate-200', async ({ page }) => {
    const idCell = page.locator('tbody tr').nth(0).locator('td').nth(1);
    await expect(idCell).toBeVisible();
    await expect(idCell).toHaveText('cold_open');
    const classes = await idCell.getAttribute('class');
    expect(classes).toContain('font-mono');
    expect(classes).toContain('text-slate-200');
  });

  test('B2: duration displayed as X.XX format with toFixed(2)', async ({ page }) => {
    const durationCell = page.locator('tbody tr').nth(0).locator('td').nth(2);
    await expect(durationCell).toHaveText('15.29');
    const durationCell2 = page.locator('tbody tr').nth(1).locator('td').nth(2);
    await expect(durationCell2).toHaveText('382.18');
  });

  test('B3: progress bar inner div.bg-green-400 width matches percentage', async ({ page }) => {
    // Row 1 (part1_economics) has progress: 65
    const row = page.locator('tbody tr').nth(1);
    const progressBar = row.locator('td').nth(4).locator('div.bg-green-400');
    await expect(progressBar).toBeVisible();
    const style = await progressBar.getAttribute('style');
    expect(style).toContain('width: 65%');
  });

  test('B4: progress text shows correct percentage', async ({ page }) => {
    const row = page.locator('tbody tr').nth(1);
    const progressText = row.locator('td').nth(4).locator('.text-xs');
    await expect(progressText).toHaveText('65%');
  });

  test('B5: 0% progress → bar width is "0%"', async ({ page }) => {
    // Row 2 (missing) has progress: 0
    const row = page.locator('tbody tr').nth(2);
    const progressBar = row.locator('td').nth(4).locator('div.bg-green-400');
    const style = await progressBar.getAttribute('style');
    expect(style).toContain('width: 0%');
  });

  test('B6: 100% progress → bar width is "100%"', async ({ page }) => {
    // Row 0 (done) has progress: 100
    const row = page.locator('tbody tr').nth(0);
    const progressBar = row.locator('td').nth(4).locator('div.bg-green-400');
    const style = await progressBar.getAttribute('style');
    expect(style).toContain('width: 100%');
  });

  test('B7: multiple sections with different progress render correctly', async ({ page }) => {
    const rows = page.locator('tbody tr');
    await expect(rows).toHaveCount(4);
    // Verify each row's progress text
    await expect(rows.nth(0).locator('td').nth(4).locator('.text-xs')).toHaveText('100%');
    await expect(rows.nth(1).locator('td').nth(4).locator('.text-xs')).toHaveText('65%');
    await expect(rows.nth(2).locator('td').nth(4).locator('.text-xs')).toHaveText('0%');
    await expect(rows.nth(3).locator('td').nth(4).locator('.text-xs')).toHaveText('0%');
  });

  test('B8: screenshot — table with mixed statuses and progress', async ({ page }) => {
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-B8-table-progress.png'),
      fullPage: true,
    });
  });
});

// ── Group C: Render Mode & Payload Logic (9 tests) ───────────────────────────

test.describe('Stage 9 QA · C: Render Mode & Payload Logic', () => {
  test('C1: default render mode is "all"', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    const select = page.getByTestId('render-mode-select');
    await expect(select).toHaveValue('all');
  });

  test('C2: "All" mode sends all section IDs in POST', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/render/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-all-job' }),
      });
    });
    await navigateToStage9(page);

    const select = page.getByTestId('render-mode-select');
    await expect(select).toHaveValue('all');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(1000);

    expect(capturedBody).not.toBeNull();
    expect(capturedBody.sections).toEqual([
      'cold_open', 'part1_economics', 'part2_paradigm_shift', 'part3_mold',
    ]);
  });

  test('C3: "Missing" mode sends only missing/zero-progress section IDs', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/render/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-missing-job' }),
      });
    });
    await navigateToStage9(page);

    await page.getByTestId('render-mode-select').selectOption('missing');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(1000);

    expect(capturedBody).not.toBeNull();
    // missing status or progress===0 → part2_paradigm_shift and part3_mold
    expect(capturedBody.sections).toContain('part2_paradigm_shift');
    expect(capturedBody.sections).toContain('part3_mold');
    expect(capturedBody.sections).not.toContain('cold_open');
  });

  test('C4: "Selected" mode sends only checked section IDs', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/render/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-selected-job' }),
      });
    });
    await navigateToStage9(page);

    // Check only the first and third rows
    await page.locator('tbody tr').nth(0).locator('input[type="checkbox"]').check();
    await page.locator('tbody tr').nth(2).locator('input[type="checkbox"]').check();

    await page.getByTestId('render-mode-select').selectOption('selected');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(1000);

    expect(capturedBody).not.toBeNull();
    expect(capturedBody.sections).toEqual(['cold_open', 'part2_paradigm_shift']);
  });

  test('C5: "Selected" mode with no checkboxes shows error', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    await page.getByTestId('render-mode-select').selectOption('selected');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(500);

    const errorDiv = page.locator('div.bg-red-900\\/50', { hasText: 'No sections selected for render.' });
    await expect(errorDiv).toBeVisible();
  });

  test('C6: error "No sections selected" displayed in red pill', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    await page.getByTestId('render-mode-select').selectOption('selected');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(500);

    const errorDiv = page.locator('div.bg-red-900\\/50');
    await expect(errorDiv).toBeVisible();
    const classes = await errorDiv.getAttribute('class');
    expect(classes).toContain('text-red-300');
    expect(classes).toContain('text-sm');
  });

  test('C7: re-render ↺ sends POST with single section ID', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/render/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'rerender-single' }),
      });
    });
    await navigateToStage9(page);

    // Click re-render on 3rd row (part2_paradigm_shift)
    await page.locator('tbody tr').nth(2).locator('button[title="Re-render"]').click();
    await page.waitForTimeout(1000);

    expect(capturedBody).not.toBeNull();
    expect(capturedBody.sections).toEqual(['part2_paradigm_shift']);
  });

  test('C8: re-render auto-checks the section checkbox', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);

    // Mock the render endpoint to avoid errors
    await page.route('**/api/pipeline/render/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'rerender-auto-check' }),
      })
    );

    const checkbox = page.locator('tbody tr').nth(2).locator('input[type="checkbox"]');
    await expect(checkbox).not.toBeChecked();

    await page.locator('tbody tr').nth(2).locator('button[title="Re-render"]').click();
    await page.waitForTimeout(500);

    await expect(checkbox).toBeChecked();
  });

  test('C9: screenshot — render mode dropdown', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-C9-render-mode.png'),
      fullPage: true,
    });
  });
});

// ── Group D: Stitch Button & Full Video Panel (8 tests) ──────────────────────

test.describe('Stage 9 QA · D: Stitch Button & Full Video Panel', () => {
  test('D1: stitch button enabled when no renders in progress (bg-emerald-600)', async ({ page }) => {
    // All sections done or missing (none rendering with 0<progress<100)
    const noActiveRenderSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
      { id: 'part2', durationSeconds: 0, status: 'missing', progress: 0 },
    ];
    await navigateWithMockedStatus(page, noActiveRenderSections, FULL_VIDEO_NONE);

    const stitchBtn = page.getByTestId('stitch-full-video-button');
    await expect(stitchBtn).toBeEnabled();
    const classes = await stitchBtn.getAttribute('class');
    expect(classes).toContain('bg-emerald-600');
    expect(classes).toContain('text-white');
  });

  test('D2: stitch button disabled during active renders (bg-slate-700)', async ({ page }) => {
    // part1_economics has 0<progress<100 → renders in progress
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);

    const stitchBtn = page.getByTestId('stitch-full-video-button');
    await expect(stitchBtn).toBeDisabled();
    const classes = await stitchBtn.getAttribute('class');
    expect(classes).toContain('bg-slate-700');
    expect(classes).toContain('text-slate-400');
    expect(classes).toContain('cursor-not-allowed');
  });

  test('D3: stitch sends POST /api/pipeline/stitch/run', async ({ page }) => {
    const noActiveRenderSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
    ];
    let stitchCalled = false;
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: noActiveRenderSections, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/stitch/run', async (route) => {
      stitchCalled = true;
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'stitch-123' }),
      });
    });
    await navigateToStage9(page);

    await page.getByTestId('stitch-full-video-button').click();
    await page.waitForTimeout(1000);

    expect(stitchCalled).toBe(true);
  });

  test('D4: full video panel hidden when fullVideo.exists=false', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    // The "Full Video" panel has a div with text "Full Video" (not the Stitch button)
    await expect(page.locator('div.font-semibold', { hasText: 'Full Video' })).not.toBeVisible();
    await expect(page.locator('button', { hasText: 'Continue' })).not.toBeVisible();
  });

  test('D5: full video panel shows size (formatBytes: "1.50 GB")', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_EXISTS);
    const panel = page.locator('text=Full Video').first();
    await expect(panel).toBeVisible();
    await expect(page.locator('text=1.50 GB')).toBeVisible();
  });

  test('D6: full video panel shows duration as "120.50s"', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_EXISTS);
    await expect(page.locator('text=120.50s')).toBeVisible();
  });

  test('D7: "Continue →" button present with bg-emerald-600', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_EXISTS);
    const btn = page.locator('button', { hasText: 'Continue →' });
    await expect(btn).toBeVisible();
    const classes = await btn.getAttribute('class');
    expect(classes).toContain('bg-emerald-600');
  });

  test('D8: screenshot — full video panel visible', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_EXISTS);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-D8-full-video-panel.png'),
      fullPage: true,
    });
  });
});

// ── Group E: Active Renders Panel & SSE Progress (8 tests) ───────────────────

test.describe('Stage 9 QA · E: Active Renders Panel & SSE Progress', () => {
  test('E1: active renders panel hidden when no sections have 0<progress<100', async ({ page }) => {
    const noActiveSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
      { id: 'part2', durationSeconds: 0, status: 'missing', progress: 0 },
    ];
    await navigateWithMockedStatus(page, noActiveSections, FULL_VIDEO_NONE);
    await expect(page.locator('h3', { hasText: 'Active Renders' })).not.toBeVisible();
  });

  test('E2: panel appears when a section has progress between 1-99', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    // part1_economics has progress: 65
    await expect(page.locator('h3', { hasText: 'Active Renders' })).toBeVisible();
  });

  test('E3: panel shows section ID and progress bar', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    const panel = page.locator('h3', { hasText: 'Active Renders' }).locator('..');
    await expect(panel.locator('text=part1_economics')).toBeVisible();
    const progressBar = panel.locator('div.bg-green-400');
    await expect(progressBar).toBeVisible();
    const style = await progressBar.getAttribute('style');
    expect(style).toContain('width: 65%');
  });

  test('E4: only top 3 active renders shown', async ({ page }) => {
    const manySections = [
      { id: 'sec_a', durationSeconds: 10, status: 'rendering', progress: 20 },
      { id: 'sec_b', durationSeconds: 10, status: 'rendering', progress: 40 },
      { id: 'sec_c', durationSeconds: 10, status: 'rendering', progress: 60 },
      { id: 'sec_d', durationSeconds: 10, status: 'rendering', progress: 80 },
    ];
    await navigateWithMockedStatus(page, manySections, FULL_VIDEO_NONE);

    const panel = page.locator('h3', { hasText: 'Active Renders' }).locator('..');
    // Only 3 progress bars in the active renders panel
    const bars = panel.locator('div.bg-green-400');
    await expect(bars).toHaveCount(3);

    // sec_d (4th) should NOT be in the active renders panel
    // It filters first 3 from sections.filter(...)
    await expect(panel.locator('text=sec_a')).toBeVisible();
    await expect(panel.locator('text=sec_b')).toBeVisible();
    await expect(panel.locator('text=sec_c')).toBeVisible();
    await expect(panel.locator('text=sec_d')).not.toBeVisible();
  });

  test('E5: SSE section-progress event updates progress in section table', async ({ page }) => {
    // Start with a rendering section at 10%
    const sections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'rendering', progress: 10 },
    ];

    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections, fullVideo: FULL_VIDEO_NONE }),
      })
    );

    // Set up SSE stream that sends a progress event
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: {
          'Content-Type': 'text/event-stream',
          'Cache-Control': 'no-cache',
          'Connection': 'keep-alive',
        },
        body: [
          'data: {"type":"section-progress","sectionId":"cold_open","percent":75}\n\n',
        ].join(''),
      })
    );

    // Mock render run to return jobId (triggers SSE subscription)
    await page.route('**/api/pipeline/render/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'sse-test-job' }),
      })
    );

    await navigateToStage9(page);

    // Trigger a render to get a jobId → which triggers SSE
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(2000);

    // After SSE update, progress should show 75%
    const progressText = page.locator('tbody tr').nth(0).locator('td').nth(4).locator('.text-xs');
    await expect(progressText).toHaveText('75%');
  });

  test('E6: SSE render-complete event reloads status', async ({ page }) => {
    const initialSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'rendering', progress: 50 },
    ];
    const completedSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
    ];

    let statusCallCount = 0;
    await page.route('**/api/pipeline/render/status', (route) => {
      statusCallCount++;
      const data = statusCallCount <= 1 ? initialSections : completedSections;
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: data, fullVideo: FULL_VIDEO_NONE }),
      });
    });

    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"render-complete"}\n\n',
      })
    );

    await page.route('**/api/pipeline/render/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'sse-complete-job' }),
      })
    );

    await navigateToStage9(page);

    // Trigger render to start SSE
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(2000);

    // After render-complete, status is reloaded → should show "Rendered"
    await expect(page.locator('span.rounded-full', { hasText: 'Rendered' })).toBeVisible({ timeout: 5000 });
  });

  test('E7: progress bar width transitions with progress', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    // Active renders panel bar for part1_economics
    const panel = page.locator('h3', { hasText: 'Active Renders' }).locator('..');
    const bar = panel.locator('div.bg-green-400').first();
    const classes = await bar.getAttribute('class');
    expect(classes).toContain('transition-all');
  });

  test('E8: screenshot — active renders panel with progress bars', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-E8-active-renders.png'),
      fullPage: true,
    });
  });
});

// ── Group F: Preview Modal Behavior (7 tests) ────────────────────────────────

test.describe('Stage 9 QA · F: Preview Modal Behavior', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
  });

  test('F1: preview ▶ click opens modal with "Preview — {sectionId}" header', async ({ page }) => {
    // Click preview on row 0 (cold_open, status=done)
    const previewBtn = page.locator('tbody tr').nth(0).locator('button[title="Preview"]');
    await previewBtn.click();
    await page.waitForTimeout(500);
    await expect(page.locator('text=Preview — cold_open')).toBeVisible();
  });

  test('F2: modal contains <video> element with correct src', async ({ page }) => {
    const previewBtn = page.locator('tbody tr').nth(0).locator('button[title="Preview"]');
    await previewBtn.click();
    await page.waitForTimeout(500);

    const video = page.locator('.fixed video');
    await expect(video).toBeAttached();
    const src = await video.getAttribute('src');
    expect(src).toBe('/api/video/outputs/sections/cold_open.mp4');
  });

  test('F3: close button (✕) closes modal', async ({ page }) => {
    const previewBtn = page.locator('tbody tr').nth(0).locator('button[title="Preview"]');
    await previewBtn.click();
    await expect(page.locator('text=Preview — cold_open')).toBeVisible();

    await page.locator('.fixed button', { hasText: '✕' }).click();
    await page.waitForTimeout(300);
    await expect(page.locator('text=Preview — cold_open')).not.toBeVisible();
  });

  test('F4: overlay click closes modal', async ({ page }) => {
    const previewBtn = page.locator('tbody tr').nth(0).locator('button[title="Preview"]');
    await previewBtn.click();
    await expect(page.locator('text=Preview — cold_open')).toBeVisible();

    // Click top-left of overlay (outside modal content)
    const overlay = page.locator('.fixed.inset-0');
    await overlay.click({ position: { x: 10, y: 10 } });
    await page.waitForTimeout(300);
    await expect(page.locator('text=Preview — cold_open')).not.toBeVisible();
  });

  test('F5: preview button disabled for missing sections', async ({ page }) => {
    // Row 2 is part2_paradigm_shift (missing)
    const btn = page.locator('tbody tr').nth(2).locator('button[title="Not yet rendered"]');
    await expect(btn).toBeVisible();
    await expect(btn).toBeDisabled();
  });

  test('F6: clicking disabled preview button does NOT open modal', async ({ page }) => {
    const btn = page.locator('tbody tr').nth(2).locator('button[title="Not yet rendered"]');
    await btn.click({ force: true });
    await page.waitForTimeout(300);
    await expect(page.locator('text=Preview —')).not.toBeVisible();
  });

  test('F7: screenshot — preview modal open', async ({ page }) => {
    const previewBtn = page.locator('tbody tr').nth(0).locator('button[title="Preview"]');
    await previewBtn.click();
    await page.waitForTimeout(500);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-F7-preview-modal.png'),
      fullPage: true,
    });
  });
});

// ── Group G: Error States & Network Failures (8 tests) ───────────────────────

test.describe('Stage 9 QA · G: Error States & Network Failures', () => {
  test('G1: status API 500 → error "Failed to load render status."', async ({ page }) => {
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{}' })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await navigateToStage9(page);

    const errorDiv = page.locator('div.bg-red-900\\/50', { hasText: 'Failed to load render status.' });
    await expect(errorDiv).toBeVisible({ timeout: 5000 });
  });

  test('G2: render POST 500 → error "Failed to start render job."', async ({ page }) => {
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/render/run', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{}' })
    );
    await navigateToStage9(page);

    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(1000);

    const errorDiv = page.locator('div.bg-red-900\\/50', { hasText: 'Failed to start render job.' });
    await expect(errorDiv).toBeVisible();
  });

  test('G3: stitch POST 500 → error "Failed to stitch full video."', async ({ page }) => {
    const noActiveSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
    ];
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: noActiveSections, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/stitch/run', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{}' })
    );
    await navigateToStage9(page);

    await page.getByTestId('stitch-full-video-button').click();
    await page.waitForTimeout(1000);

    const errorDiv = page.locator('div.bg-red-900\\/50', { hasText: 'Failed to stitch full video.' });
    await expect(errorDiv).toBeVisible();
  });

  test('G4: render POST abort → no crash, heading still visible', async ({ page }) => {
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/render/run', (route) => route.abort());
    await navigateToStage9(page);

    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
  });

  test('G5: stitch POST abort → no crash', async ({ page }) => {
    const noActiveSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
    ];
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: noActiveSections, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/stitch/run', (route) => route.abort());
    await navigateToStage9(page);

    await page.getByTestId('stitch-full-video-button').click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
  });

  test('G6: error clears when new action is attempted', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);

    // Trigger "No sections selected" error
    await page.getByTestId('render-mode-select').selectOption('selected');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(500);
    await expect(page.locator('div.bg-red-900\\/50')).toBeVisible();

    // Now switch to "all" and render again → error should clear
    await page.getByTestId('render-mode-select').selectOption('all');

    // Mock the render endpoint
    await page.route('**/api/pipeline/render/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'clear-error-job' }),
      })
    );
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(500);

    await expect(page.locator('div.bg-red-900\\/50')).not.toBeVisible();
  });

  test('G7: stitching state resets after failure', async ({ page }) => {
    const noActiveSections = [
      { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
    ];
    await page.route('**/api/pipeline/render/status', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: noActiveSections, fullVideo: FULL_VIDEO_NONE }),
      })
    );
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );
    await page.route('**/api/pipeline/stitch/run', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{}' })
    );
    await navigateToStage9(page);

    const stitchBtn = page.getByTestId('stitch-full-video-button');
    await stitchBtn.click();
    await page.waitForTimeout(1000);

    // After failure, button should be enabled again (not stuck in disabled stitching state)
    await expect(stitchBtn).toBeEnabled();
    const classes = await stitchBtn.getAttribute('class');
    expect(classes).toContain('bg-emerald-600');
  });

  test('G8: screenshot — error state', async ({ page }) => {
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, FULL_VIDEO_NONE);
    await page.getByTestId('render-mode-select').selectOption('selected');
    await page.getByTestId('render-sections-button').click();
    await page.waitForTimeout(500);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-G8-error-state.png'),
      fullPage: true,
    });
  });
});

// ── Group H: Edge Cases (6 tests) ────────────────────────────────────────────

test.describe('Stage 9 QA · H: Edge Cases', () => {
  test('H1: empty sections → "No sections found." in table', async ({ page }) => {
    await navigateWithMockedStatus(page, [], FULL_VIDEO_NONE);
    await expect(page.locator('text=No sections found.')).toBeVisible();
  });

  test('H2: "Loading..." text visible during slow status fetch', async ({ page }) => {
    // Delay the status response by 3s
    await page.route('**/api/pipeline/render/status', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS, fullVideo: FULL_VIDEO_NONE }),
      });
    });
    await page.route('**/api/pipeline/render/stream**', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );

    await navigateToStage9(page);

    // "Loading..." should be visible while waiting
    await expect(page.locator('text=Loading...')).toBeVisible({ timeout: 2000 });
  });

  test('H3: formatBytes: 0 → "—"', async ({ page }) => {
    const fullVideoZero = { exists: true, sizeBytes: 0, durationSeconds: 10 };
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, fullVideoZero);
    // The size should show "—" for 0 bytes
    await expect(page.locator('text=Size: —')).toBeVisible();
  });

  test('H4: formatBytes: 1073741824 → "1.00 GB"', async ({ page }) => {
    const fullVideoGB = { exists: true, sizeBytes: 1073741824, durationSeconds: 60 };
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, fullVideoGB);
    await expect(page.locator('text=1.00 GB')).toBeVisible();
  });

  test('H5: formatBytes: 1048576 → "1.00 MB"', async ({ page }) => {
    const fullVideoMB = { exists: true, sizeBytes: 1048576, durationSeconds: 30 };
    await navigateWithMockedStatus(page, ALL_STATUS_SECTIONS, fullVideoMB);
    await expect(page.locator('text=1.00 MB')).toBeVisible();
  });

  test('H6: screenshot — empty/loading state', async ({ page }) => {
    await navigateWithMockedStatus(page, [], FULL_VIDEO_NONE);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage9-H6-empty-state.png'),
      fullPage: true,
    });
  });
});
