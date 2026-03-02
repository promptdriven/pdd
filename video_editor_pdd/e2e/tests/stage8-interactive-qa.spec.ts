import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

// ── Shared mock data ──────────────────────────────────────────────────────────

const ALL_STATUS_SECTIONS = [
  {
    id: 'cold_open',
    label: 'Cold Open',
    components: [
      { name: 'TitleCard', status: 'done', error: null },
      { name: 'IntroScene', status: 'missing', error: null },
      { name: 'FailedRender', status: 'error', error: 'Remotion render timeout after 60s' },
      { name: 'ActiveRender', status: 'running', error: null },
      { name: 'QueuedRender', status: 'pending', error: null },
    ],
    wrappers: [{ name: 'cold_openWrapper', status: 'done', error: null }],
  },
  {
    id: 'part1',
    label: 'Part 1: Economics',
    components: [{ name: 'EconOverview', status: 'done', error: null }],
    wrappers: [{ name: 'part1Wrapper', status: 'missing', error: null }],
  },
];

const MIXED_MANIFEST = [
  { filename: 'cold_open.mp4', expected: true, present: true },
  { filename: 'part1_econ.mp4', expected: true, present: false },
  { filename: 'bonus_clip.mp4', expected: false, present: false },
  { filename: 'part2_shift.mp4', expected: false, present: true },
];

// ── Helpers ───────────────────────────────────────────────────────────────────

async function navigateToStage8(page: import('@playwright/test').Page) {
  await page.goto('/');
  await page.waitForLoadState('networkidle');

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });
  await page.waitForTimeout(1000);

  const heading = page.locator('h2', { hasText: 'Stage 8' });

  await sidebar.locator('div.cursor-pointer').nth(7).click();
  try {
    await expect(heading).toBeVisible({ timeout: 3000 });
  } catch {
    await page.waitForTimeout(500);
    await page.evaluate(() => {
      const items = document.querySelectorAll('aside div.cursor-pointer');
      if (items[7]) (items[7] as HTMLElement).click();
    });
    try {
      await expect(heading).toBeVisible({ timeout: 3000 });
    } catch {
      await page.waitForTimeout(1000);
      await sidebar.locator('div.cursor-pointer').nth(7).click({ force: true });
      await expect(heading).toBeVisible({ timeout: 10000 });
    }
  }

  await page.waitForTimeout(500);
}

async function navigateWithMockedData(
  page: import('@playwright/test').Page,
  sections: unknown[],
  manifest: unknown[],
) {
  await page.route('**/api/pipeline/compositions/list', (route) =>
    route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ sections }),
    })
  );
  await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
    route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify(manifest),
    })
  );
  // Mock SSE stream to prevent hanging EventSource
  await page.route('**/api/jobs/*/stream', (route) =>
    route.fulfill({
      status: 200,
      headers: { 'Content-Type': 'text/event-stream' },
      body: 'data: {"type":"connected"}\n\n',
    })
  );

  await navigateToStage8(page);
}

// ── Group A: StatusBadge Rendering & CSS (8 tests) ────────────────────────────

test.describe('Stage 8 QA · A: StatusBadge Rendering & CSS', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);
  });

  test('A1: done badge shows "Done" with green classes', async ({ page }) => {
    const row = page.locator('[data-testid="component-row-TitleCard"]');
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Done' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-green-900/50');
    expect(classes).toContain('text-green-300');
    expect(classes).toContain('border-green-700');
  });

  test('A2: missing badge shows "Missing" with yellow classes', async ({ page }) => {
    const row = page.locator('[data-testid="component-row-IntroScene"]');
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Missing' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-yellow-900/50');
    expect(classes).toContain('text-yellow-300');
    expect(classes).toContain('border-yellow-700');
  });

  test('A3: error badge shows "Error" with red classes', async ({ page }) => {
    const row = page.locator('[data-testid="component-row-FailedRender"]');
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Error' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-red-900/50');
    expect(classes).toContain('text-red-300');
    expect(classes).toContain('border-red-700');
  });

  test('A4: running badge shows "Running" with blue classes', async ({ page }) => {
    const row = page.locator('[data-testid="component-row-ActiveRender"]');
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Running' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-blue-900/50');
    expect(classes).toContain('text-blue-300');
    expect(classes).toContain('border-blue-700');
  });

  test('A5: pending badge shows "Pending" with slate classes', async ({ page }) => {
    const row = page.locator('[data-testid="component-row-QueuedRender"]');
    await expect(row).toBeVisible();
    const badge = row.locator('span.rounded-full', { hasText: 'Pending' });
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('bg-slate-700');
    expect(classes).toContain('text-slate-200');
    expect(classes).toContain('border-slate-600');
  });

  test('A6: all 5 badge types rendered simultaneously', async ({ page }) => {
    for (const label of ['Done', 'Missing', 'Error', 'Running', 'Pending']) {
      await expect(page.locator('span.rounded-full', { hasText: label }).first()).toBeVisible();
    }
  });

  test('A7: badge has base classes rounded-full border px-2 py-0.5 text-xs font-medium', async ({ page }) => {
    const badge = page.locator('span.rounded-full', { hasText: 'Done' }).first();
    await expect(badge).toBeVisible();
    const classes = await badge.getAttribute('class');
    expect(classes).toContain('rounded-full');
    expect(classes).toContain('border');
    expect(classes).toContain('px-2');
    expect(classes).toContain('py-0.5');
    expect(classes).toContain('text-xs');
    expect(classes).toContain('font-medium');
  });

  test('A8: screenshot — all five status badges', async ({ page }) => {
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-A8-status-badges.png'),
      fullPage: true,
    });
  });
});

// ── Group B: Staging Manifest Table Cells (8 tests) ───────────────────────────

test.describe('Stage 8 QA · B: Staging Manifest Table Cells', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);
  });

  test('B1: expected=true shows green ✓ (text-green-600)', async ({ page }) => {
    // cold_open.mp4: expected=true
    const rows = page.locator('tbody tr');
    const firstRow = rows.nth(0);
    const expectedCell = firstRow.locator('td').nth(1);
    const checkmark = expectedCell.locator('span.text-green-600');
    await expect(checkmark).toBeVisible();
    await expect(checkmark).toHaveText('✓');
  });

  test('B2: expected=false shows slate ✗ (text-slate-400)', async ({ page }) => {
    // bonus_clip.mp4: expected=false (row index 2)
    const rows = page.locator('tbody tr');
    const row = rows.nth(2);
    const expectedCell = row.locator('td').nth(1);
    const cross = expectedCell.locator('span.text-slate-400');
    await expect(cross).toBeVisible();
    await expect(cross).toHaveText('✗');
  });

  test('B3: present=true shows green ✓ (text-green-600)', async ({ page }) => {
    // cold_open.mp4: present=true (row index 0)
    const rows = page.locator('tbody tr');
    const firstRow = rows.nth(0);
    const presentCell = firstRow.locator('td').nth(2);
    const checkmark = presentCell.locator('span.text-green-600');
    await expect(checkmark).toBeVisible();
    await expect(checkmark).toHaveText('✓');
  });

  test('B4: present=false shows red ✗ (text-red-500)', async ({ page }) => {
    // part1_econ.mp4: present=false (row index 1)
    const rows = page.locator('tbody tr');
    const row = rows.nth(1);
    const presentCell = row.locator('td').nth(2);
    const cross = presentCell.locator('span.text-red-500');
    await expect(cross).toBeVisible();
    await expect(cross).toHaveText('✗');
  });

  test('B5: "Stage Now" only when expected=true AND present=false', async ({ page }) => {
    const stageNowButtons = page.locator('button', { hasText: 'Stage Now' });
    // Only part1_econ.mp4 qualifies (expected=true, present=false)
    await expect(stageNowButtons).toHaveCount(1);

    // The button should be in the part1_econ.mp4 row (index 1)
    const rows = page.locator('tbody tr');
    const row1 = rows.nth(1);
    await expect(row1).toContainText('part1_econ.mp4');
    await expect(row1.locator('button', { hasText: 'Stage Now' })).toBeVisible();
  });

  test('B6: "Stage Now" click fires POST with correct filename', async ({ page }) => {
    let requestBody: unknown = null;
    await page.route('**/api/pipeline/asset-staging/run', (route) => {
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'stage-single-job' }),
      });
    });

    const stageNowBtn = page.locator('button', { hasText: 'Stage Now' });
    await expect(stageNowBtn).toBeVisible();
    await stageNowBtn.click();
    await page.waitForTimeout(500);

    expect(requestBody).not.toBeNull();
    expect((requestBody as { files: string[] }).files).toContain('part1_econ.mp4');
  });

  test('B7: filename text is in text-slate-200', async ({ page }) => {
    const rows = page.locator('tbody tr');
    const firstRow = rows.nth(0);
    const filenameCell = firstRow.locator('td').nth(0);
    const classes = await filenameCell.getAttribute('class');
    expect(classes).toContain('text-slate-200');
  });

  test('B8: screenshot — staging manifest table with mixed entries', async ({ page }) => {
    const table = page.locator('table');
    await table.scrollIntoViewIfNeeded();
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-B8-staging-manifest.png'),
      fullPage: true,
    });
  });
});

// ── Group C: Busy States & Button Text (9 tests) ─────────────────────────────

test.describe('Stage 8 QA · C: Busy States & Button Text', () => {
  test('C1: "Generate All" shows "Generating..." during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-gen-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const btn = page.locator('button', { hasText: 'Generate All Compositions' });
    await expect(btn).toBeVisible();
    await btn.click();

    // Should immediately show busy text
    await expect(page.locator('button', { hasText: 'Generating...' })).toBeVisible({ timeout: 2000 });
  });

  test('C2: "Generate All" button disabled during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-gen-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const btn = page.locator('button', { hasText: 'Generate All Compositions' });
    await btn.click();
    await expect(page.locator('button', { hasText: 'Generating...' })).toBeDisabled();
  });

  test('C3: "Stage All Missing" shows "Staging..." during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-stage-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const btn = page.locator('button', { hasText: 'Stage All Missing' });
    await expect(btn).toBeVisible();
    await btn.click();

    await expect(page.locator('button', { hasText: 'Staging...' })).toBeVisible({ timeout: 2000 });
  });

  test('C4: "Stage All Missing" button disabled during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-stage-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const btn = page.locator('button', { hasText: 'Stage All Missing' });
    await btn.click();
    await expect(page.locator('button', { hasText: 'Staging...' })).toBeDisabled();
  });

  test('C5: per-component ↺ shows "..." during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-regen-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const row = page.locator('[data-testid="component-row-TitleCard"]');
    await expect(row).toBeVisible();
    const regenBtn = row.locator('button', { hasText: '↺' });
    await expect(regenBtn).toBeVisible();
    await regenBtn.click();

    // Button should now show "..."
    await expect(row.locator('button', { hasText: '...' })).toBeVisible({ timeout: 2000 });
  });

  test('C6: per-component ↺ disabled during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-regen-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const row = page.locator('[data-testid="component-row-TitleCard"]');
    const regenBtn = row.locator('button', { hasText: '↺' });
    await regenBtn.click();

    await expect(row.locator('button', { hasText: '...' })).toBeDisabled();
  });

  test('C7: per-file "Stage Now" shows "..." during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-stage-single' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const stageBtn = page.locator('button', { hasText: 'Stage Now' });
    await expect(stageBtn).toBeVisible();
    await stageBtn.click();

    // Should show "..." in that cell
    const row = page.locator('tbody tr').nth(1);
    await expect(row.locator('button', { hasText: '...' })).toBeVisible({ timeout: 2000 });
  });

  test('C8: per-wrapper ↺ shows "..." during pending POST', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'slow-wrapper-regen' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const wrapperSection = page.locator('h4', { hasText: 'Section Wrappers' }).locator('..');
    await wrapperSection.scrollIntoViewIfNeeded();
    const regenBtn = wrapperSection.locator('button', { hasText: '↺' }).first();
    await expect(regenBtn).toBeVisible();
    await regenBtn.click();

    await expect(wrapperSection.locator('button', { hasText: '...' }).first()).toBeVisible({ timeout: 2000 });
  });

  test('C9: screenshot — busy generating state', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'screenshot-gen-job' }),
      });
    });
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const btn = page.locator('button', { hasText: 'Generate All Compositions' });
    await btn.click();
    await expect(page.locator('button', { hasText: 'Generating...' })).toBeVisible();

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-C9-busy-generating.png'),
      fullPage: true,
    });
  });
});

// ── Group D: Job Logs Auto-Open & SseLogPanel (8 tests) ──────────────────────

test.describe('Stage 8 QA · D: Job Logs Auto-Open & SseLogPanel', () => {
  test('D1: Job Logs panel closed by default (shows "Show")', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn).toBeVisible();
    await expect(jobLogsBtn.locator('span', { hasText: 'Show' })).toBeVisible();
  });

  test('D2: Generate All auto-opens Job Logs (shows "Hide")', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'gen-all-auto-open' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(500);

    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();
  });

  test('D3: Stage All Missing auto-opens Job Logs', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'stage-all-auto-open' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const stageBtn = page.locator('button', { hasText: 'Stage All Missing' });
    await stageBtn.click();
    await page.waitForTimeout(500);

    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();
  });

  test('D4: per-component regenerate auto-opens Job Logs', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'regen-auto-open' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const row = page.locator('[data-testid="component-row-TitleCard"]');
    const regenBtn = row.locator('button', { hasText: '↺' });
    await regenBtn.click();
    await page.waitForTimeout(500);

    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();
  });

  test('D5: SseLogPanel shows "Waiting for logs…" when no events', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'waiting-job' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('text=Waiting for logs…')).toBeVisible();
  });

  test('D6: SseLogPanel renders inside Job Logs collapsible with bg-slate-800', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'log-panel-bg-job' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(500);

    // The SseLogPanel container has bg-slate-800
    const logContainer = page.locator('div.bg-slate-800').filter({ has: page.locator('text=Waiting for logs…') });
    await expect(logContainer).toBeVisible();
  });

  test('D7: Job Logs can be manually closed while active', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'close-while-active' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(500);

    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();

    // Close it manually
    await jobLogsBtn.click();
    await expect(jobLogsBtn.locator('span', { hasText: 'Show' })).toBeVisible();
    // Log content should not be visible
    await expect(page.locator('text=Waiting for logs…')).not.toBeVisible();
  });

  test('D8: screenshot — Job Logs open', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'screenshot-log-job' }),
      })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(500);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-D8-job-logs-open.png'),
      fullPage: true,
    });
  });
});

// ── Group E: Edge Cases — Empty & Error States (8 tests) ─────────────────────

test.describe('Stage 8 QA · E: Edge Cases — Empty & Error States', () => {
  test('E1: loading state shows "Loading components…" during slow fetch', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      });
    });
    await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );
    await page.route('**/api/jobs/*/stream', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );

    await navigateToStage8(page);
    await expect(page.locator('text=Loading components…')).toBeVisible();
  });

  test('E2: empty sections shows Components (0)', async ({ page }) => {
    await navigateWithMockedData(page, [], []);
    const heading = page.locator('h3', { hasText: /Components\s*\(0\)/ });
    await expect(heading).toBeVisible();
  });

  test('E3: empty components in section shows "No components"', async ({ page }) => {
    const emptySections = [
      { id: 'empty_section', label: 'Empty Section', components: [], wrappers: [] },
    ];
    await navigateWithMockedData(page, emptySections, []);

    await expect(page.locator('text=No components')).toBeVisible();
  });

  test('E4: empty staging manifest shows "No staging entries found."', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);
    await expect(page.locator('text=No staging entries found.')).toBeVisible();
  });

  test('E5: list API 500 shows red error pill', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Internal Server Error' })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );
    await page.route('**/api/jobs/*/stream', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );

    await navigateToStage8(page);
    // Wait for loading to finish
    await page.waitForTimeout(2000);

    const errorPill = page.locator('p.bg-red-900\\/50', { hasText: /Failed to load compositions/ });
    await expect(errorPill).toBeVisible();
  });

  test('E6: manifest API 500 shows separate red error pill', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Internal Server Error' })
    );
    await page.route('**/api/jobs/*/stream', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );

    await navigateToStage8(page);
    await page.waitForTimeout(2000);

    const errorPill = page.locator('p.bg-red-900\\/50', { hasText: /Failed to load.*manifest/ });
    await expect(errorPill).toBeVisible();
  });

  test('E7: both APIs failing shows two red error pills', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await page.route('**/api/jobs/*/stream', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );

    await navigateToStage8(page);
    await page.waitForTimeout(2000);

    const errorPills = page.locator('p.bg-red-900\\/50');
    await expect(errorPills).toHaveCount(2);
  });

  test('E8: screenshot — dual error state', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await page.route('**/api/jobs/*/stream', (route) =>
      route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: 'data: {"type":"connected"}\n\n',
      })
    );

    await navigateToStage8(page);
    await page.waitForTimeout(2000);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-E8-dual-error.png'),
      fullPage: true,
    });
  });
});

// ── Group F: localStorage Persistence (7 tests) ──────────────────────────────

test.describe('Stage 8 QA · F: localStorage Persistence', () => {
  test('F1: collapsing section persists to localStorage', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    // Collapse Cold Open
    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Show' })).toBeVisible();

    const stored = await page.evaluate(() =>
      localStorage.getItem('stage8-collapsed-sections')
    );
    expect(stored).not.toBeNull();
    const parsed = JSON.parse(stored!);
    expect(parsed['cold_open']).toBe(true);
  });

  test('F2: expanding updates localStorage', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    // Collapse
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Show' })).toBeVisible();
    // Expand
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Hide' })).toBeVisible();

    const stored = await page.evaluate(() =>
      localStorage.getItem('stage8-collapsed-sections')
    );
    const parsed = JSON.parse(stored!);
    expect(parsed['cold_open']).toBe(false);
  });

  test('F3: collapsed state restored on re-navigation to Stage 8', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    // Collapse Cold Open
    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Show' })).toBeVisible();

    // Navigate away (click stage 1 in sidebar)
    const sidebar = page.locator('aside');
    await sidebar.locator('div.cursor-pointer').nth(0).click();
    await page.waitForTimeout(500);

    // Navigate back to Stage 8
    await sidebar.locator('div.cursor-pointer').nth(7).click();
    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(500);

    // Cold Open should still be collapsed
    const coldOpenBtn2 = page.locator('button', { hasText: 'Cold Open' });
    await expect(coldOpenBtn2.locator('span', { hasText: 'Show' })).toBeVisible();
  });

  test('F4: multiple sections collapsed independently', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    // Collapse Cold Open
    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Show' })).toBeVisible();

    // Part 1 should remain expanded
    const part1Btn = page.locator('button', { hasText: 'Part 1: Economics' });
    await expect(part1Btn.locator('span', { hasText: 'Hide' })).toBeVisible();

    const stored = await page.evaluate(() =>
      localStorage.getItem('stage8-collapsed-sections')
    );
    const parsed = JSON.parse(stored!);
    expect(parsed['cold_open']).toBe(true);
    expect(parsed['part1']).toBeUndefined();
  });

  test('F5: localStorage key is exactly "stage8-collapsed-sections"', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await coldOpenBtn.click();

    const keys = await page.evaluate(() => Object.keys(localStorage));
    expect(keys).toContain('stage8-collapsed-sections');
  });

  test('F6: collapsed section hides component rows, expanded shows them', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    // Initially expanded — TitleCard row visible
    await expect(page.locator('[data-testid="component-row-TitleCard"]')).toBeVisible();

    // Collapse Cold Open
    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await coldOpenBtn.click();

    // TitleCard row should be hidden
    await expect(page.locator('[data-testid="component-row-TitleCard"]')).not.toBeVisible();

    // Expand again
    await coldOpenBtn.click();
    await expect(page.locator('[data-testid="component-row-TitleCard"]')).toBeVisible();
  });

  test('F7: screenshot — mixed collapsed/expanded sections', async ({ page }) => {
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    // Collapse Cold Open, leave Part 1 expanded
    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Show' })).toBeVisible();

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-F7-mixed-collapse.png'),
      fullPage: true,
    });
  });
});

// ── Group G: Network Failures on POST (8 tests) ──────────────────────────────

test.describe('Stage 8 QA · G: Network Failures on POST', () => {
  test('G1: Generate All POST 500 — heading still visible, no crash', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Internal Server Error' })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
  });

  test('G2: Generate All POST abort — no crash', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) => route.abort());
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
  });

  test('G3: Stage All Missing POST 500 — no crash', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const stageBtn = page.locator('button', { hasText: 'Stage All Missing' });
    await stageBtn.click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
  });

  test('G4: Stage All Missing POST abort — no crash', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', (route) => route.abort());
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const stageBtn = page.locator('button', { hasText: 'Stage All Missing' });
    await stageBtn.click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
  });

  test('G5: per-component regenerate POST 500 — no crash', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const row = page.locator('[data-testid="component-row-TitleCard"]');
    const regenBtn = row.locator('button', { hasText: '↺' });
    await regenBtn.click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
  });

  test('G6: per-file Stage Now POST 500 — no crash', async ({ page }) => {
    await page.route('**/api/pipeline/asset-staging/run', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const stageNowBtn = page.locator('button', { hasText: 'Stage Now' });
    await expect(stageNowBtn).toBeVisible();
    await stageNowBtn.click();
    await page.waitForTimeout(1000);

    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
  });

  test('G7: button reverts from busy text after POST failure', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, []);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    // Wait for the POST to complete (failure) and button to revert
    await page.waitForTimeout(1000);

    // Button should revert to original text, not stuck on "Generating..."
    await expect(page.locator('button', { hasText: 'Generate All Compositions' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Generating...' })).not.toBeVisible();
  });

  test('G8: screenshot — resilient state after failure', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/run', (route) =>
      route.fulfill({ status: 500, contentType: 'text/plain', body: 'Error' })
    );
    await navigateWithMockedData(page, ALL_STATUS_SECTIONS, MIXED_MANIFEST);

    const genBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await genBtn.click();
    await page.waitForTimeout(1000);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage8-G8-after-failure.png'),
      fullPage: true,
    });
  });
});
