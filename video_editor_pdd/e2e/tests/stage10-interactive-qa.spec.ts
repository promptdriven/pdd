import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

// ── Shared mock data ──────────────────────────────────────────────────────────

const ALL_STATUS_SECTIONS = [
  {
    sectionId: 'cold_open',
    sectionLabel: 'Cold Open',
    passCount: 3,
    failCount: 1,
    status: 'done',
    specs: [
      { specName: 'title_visible', verdict: 'PASS', summary: 'Title card appears within 2s' },
      { specName: 'logo_centered', verdict: 'PASS', summary: 'Logo centered horizontally' },
      { specName: 'audio_sync', verdict: 'PASS', summary: 'Audio aligns with visual' },
      {
        specName: 'text_readable',
        verdict: 'FAIL',
        summary: 'Text too small at 720p',
        finding: 'Font size 8px below 12px min',
        specPath: 'specs/cold_open/text_readable.yaml',
      },
    ],
  },
  {
    sectionId: 'part1',
    sectionLabel: 'Part 1: Economics',
    passCount: 0,
    failCount: 0,
    status: 'running',
    specs: [],
  },
  {
    sectionId: 'part2',
    sectionLabel: 'Part 2: Paradigm Shift',
    passCount: 0,
    failCount: 0,
    status: 'pending',
    specs: [],
  },
  {
    sectionId: 'part3',
    sectionLabel: 'Part 3: Mold',
    passCount: 0,
    failCount: 2,
    status: 'error',
    specs: [
      {
        specName: 'scene_transition',
        verdict: 'FAIL',
        summary: 'Missing crossfade',
        finding: 'Hard cut detected',
        specPath: 'specs/part3/scene_transition.yaml',
      },
      {
        specName: 'color_grade',
        verdict: 'FAIL',
        summary: 'Color out of gamut',
        finding: 'sRGB clipping on reds',
        specPath: 'specs/part3/color_grade.yaml',
      },
    ],
  },
];

// ── Helpers ───────────────────────────────────────────────────────────────────

async function navigateToStage10(page: import('@playwright/test').Page) {
  await page.goto('/');
  await page.waitForLoadState('networkidle');

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });
  await page.waitForTimeout(1000);

  const heading = page.locator('h2', { hasText: 'Audit Results' });

  await sidebar.locator('div.cursor-pointer').nth(9).click();
  try {
    await expect(heading).toBeVisible({ timeout: 3000 });
  } catch {
    await page.waitForTimeout(500);
    await page.evaluate(() => {
      const items = document.querySelectorAll('aside div.cursor-pointer');
      if (items[9]) (items[9] as HTMLElement).click();
    });
    try {
      await expect(heading).toBeVisible({ timeout: 3000 });
    } catch {
      await page.waitForTimeout(1000);
      await sidebar.locator('div.cursor-pointer').nth(9).click({ force: true });
      await expect(heading).toBeVisible({ timeout: 10000 });
    }
  }

  await page.waitForTimeout(500);
}

async function navigateWithMockedResults(
  page: import('@playwright/test').Page,
  sections: unknown[],
) {
  // Mock audit results API
  await page.route('**/api/pipeline/audit/results', (route) =>
    route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ sections }),
    }),
  );

  // Mock SSE stream to prevent connection issues
  await page.route('**/api/pipeline/audit/stream', (route) =>
    route.fulfill({
      status: 200,
      contentType: 'text/event-stream',
      body: '',
    }),
  );

  await navigateToStage10(page);
}

// ── Group A: Status Badge Rendering & CSS ─────────────────────────────────────

test.describe('Stage 10 QA – A: Status Badge Rendering & CSS', () => {
  test('A1: done status badge shows text "done" with bg-green-800 text-green-200', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const badge = page.locator('span', { hasText: /^done$/ }).first();
    await expect(badge).toBeVisible();
    await expect(badge).toHaveClass(/bg-green-800/);
    await expect(badge).toHaveClass(/text-green-200/);
  });

  test('A2: running status badge shows text "running" with bg-amber-800 text-amber-200', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const badge = page.locator('span', { hasText: /^running$/ }).first();
    await expect(badge).toBeVisible();
    await expect(badge).toHaveClass(/bg-amber-800/);
    await expect(badge).toHaveClass(/text-amber-200/);
  });

  test('A3: error status badge shows text "error" with bg-red-800 text-red-200', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const badge = page.locator('span', { hasText: /^error$/ }).first();
    await expect(badge).toBeVisible();
    await expect(badge).toHaveClass(/bg-red-800/);
    await expect(badge).toHaveClass(/text-red-200/);
  });

  test('A4: pending status badge shows text "pending" with bg-slate-700 text-slate-200', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const badge = page.locator('span', { hasText: /^pending$/ }).first();
    await expect(badge).toBeVisible();
    await expect(badge).toHaveClass(/bg-slate-700/);
    await expect(badge).toHaveClass(/text-slate-200/);
  });

  test('A5: all four status types rendered simultaneously', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await expect(page.locator('span', { hasText: /^done$/ }).first()).toBeVisible();
    await expect(page.locator('span', { hasText: /^running$/ }).first()).toBeVisible();
    await expect(page.locator('span', { hasText: /^pending$/ }).first()).toBeVisible();
    await expect(page.locator('span', { hasText: /^error$/ }).first()).toBeVisible();
  });

  test('A6: status badge has base classes rounded text-xs px-2 py-0.5', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const badge = page.locator('span', { hasText: /^done$/ }).first();
    await expect(badge).toHaveClass(/rounded/);
    await expect(badge).toHaveClass(/text-xs/);
    await expect(badge).toHaveClass(/px-2/);
    await expect(badge).toHaveClass(/py-0\.5/);
  });

  test('A7: status badge does NOT use rounded-full', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const badges = page.locator('span', { hasText: /^(done|running|pending|error)$/ });
    const count = await badges.count();
    for (let i = 0; i < count; i++) {
      const cls = await badges.nth(i).getAttribute('class');
      expect(cls).not.toContain('rounded-full');
    }
  });

  test('A8: screenshot — all four status badges', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.waitForTimeout(500);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-A8-status-badges.png'),
      fullPage: false,
    });
  });
});

// ── Group B: Verdict Badges & Spec Detail Rows ────────────────────────────────

test.describe('Stage 10 QA – B: Verdict Badges & Spec Detail Rows', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);
    // Expand the Cold Open section (has both PASS and FAIL)
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);
  });

  test('B1: PASS verdict badge shows text "PASS" with bg-green-800 text-green-200', async ({ page }) => {
    const badge = page.locator('span', { hasText: /^PASS$/ }).first();
    await expect(badge).toBeVisible();
    await expect(badge).toHaveClass(/bg-green-800/);
    await expect(badge).toHaveClass(/text-green-200/);
  });

  test('B2: FAIL verdict badge shows text "FAIL" with bg-red-800 text-red-200', async ({ page }) => {
    const badge = page.locator('span', { hasText: /^FAIL$/ }).first();
    await expect(badge).toBeVisible();
    await expect(badge).toHaveClass(/bg-red-800/);
    await expect(badge).toHaveClass(/text-red-200/);
  });

  test('B3: spec name displayed with font-mono text-xs text-white/80', async ({ page }) => {
    const specNameCell = page.locator('.font-mono.text-xs', { hasText: 'title_visible' });
    await expect(specNameCell).toBeVisible();
    await expect(specNameCell).toHaveClass(/text-white\/80/);
  });

  test('B4: summary displayed with text-white/70', async ({ page }) => {
    const summaryCell = page.locator('.col-span-7', { hasText: 'Title card appears within 2s' });
    await expect(summaryCell).toBeVisible();
    await expect(summaryCell).toHaveClass(/text-white\/70/);
  });

  test('B5: FAIL row shows action buttons View Frame, View Spec, Create Annotation', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Frame' }).first()).toBeVisible();
    await expect(page.locator('button', { hasText: 'View Spec' }).first()).toBeVisible();
    await expect(page.locator('button', { hasText: 'Create Annotation →' }).first()).toBeVisible();
  });

  test('B6: PASS row does NOT show action buttons', async ({ page }) => {
    // PASS spec rows should not have View Frame / View Spec / Create Annotation
    // The PASS specs are title_visible, logo_centered, audio_sync
    // Count total View Frame buttons — should match FAIL count (1 in cold_open)
    const viewFrameButtons = page.locator('button', { hasText: 'View Frame' });
    await expect(viewFrameButtons).toHaveCount(1);
  });

  test('B7: both PASS and FAIL verdicts visible in same expanded section', async ({ page }) => {
    const passBadges = page.locator('span', { hasText: /^PASS$/ });
    const failBadges = page.locator('span', { hasText: /^FAIL$/ });
    expect(await passBadges.count()).toBeGreaterThanOrEqual(1);
    expect(await failBadges.count()).toBeGreaterThanOrEqual(1);
  });

  test('B8: screenshot — expanded report with mixed verdicts', async ({ page }) => {
    await page.waitForTimeout(500);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-B8-verdict-badges.png'),
      fullPage: false,
    });
  });
});

// ── Group C: Section Table Layout & Data ──────────────────────────────────────

test.describe('Stage 10 QA – C: Section Table Layout & Data', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);
  });

  test('C1: grid header shows Section, Pass, Fail, Status, Actions columns', async ({ page }) => {
    const header = page.locator('.grid.grid-cols-6.bg-white\\/5');
    await expect(header).toBeVisible();
    await expect(header.locator('div', { hasText: 'Section' })).toBeVisible();
    await expect(header.locator('div', { hasText: 'Pass' })).toBeVisible();
    await expect(header.locator('div', { hasText: 'Fail' })).toBeVisible();
    await expect(header.locator('div', { hasText: 'Status' })).toBeVisible();
    await expect(header.locator('div', { hasText: 'Actions' })).toBeVisible();
  });

  test('C2: section label displayed in row', async ({ page }) => {
    await expect(page.locator('.grid.grid-cols-6.items-center', { hasText: 'Cold Open' })).toBeVisible();
    await expect(page.locator('.grid.grid-cols-6.items-center', { hasText: 'Part 1: Economics' })).toBeVisible();
  });

  test('C3: pass count displayed correctly', async ({ page }) => {
    // Cold Open row should show passCount=3
    const coldOpenRow = page.locator('.grid.grid-cols-6.items-center', { hasText: 'Cold Open' });
    await expect(coldOpenRow).toContainText('3');
  });

  test('C4: fail count displayed correctly', async ({ page }) => {
    // Cold Open row should show failCount=1
    const coldOpenRow = page.locator('.grid.grid-cols-6.items-center', { hasText: 'Cold Open' });
    await expect(coldOpenRow).toContainText('1');
    // Part 3 row should show failCount=2
    const part3Row = page.locator('.grid.grid-cols-6.items-center', { hasText: 'Part 3: Mold' });
    await expect(part3Row).toContainText('2');
  });

  test('C5: View Report button present per section row', async ({ page }) => {
    const viewReportButtons = page.locator('button', { hasText: 'View Report' });
    await expect(viewReportButtons).toHaveCount(4); // 4 sections
  });

  test('C6: ↺ Audit button present per section row', async ({ page }) => {
    const auditButtons = page.locator('button', { hasText: '↺ Audit' });
    await expect(auditButtons).toHaveCount(4); // 4 sections
  });

  test('C7: multiple section rows rendered for multiple sections', async ({ page }) => {
    await expect(page.locator('.grid.grid-cols-6.items-center')).toHaveCount(4);
  });

  test('C8: screenshot — section table with pass/fail counts', async ({ page }) => {
    await page.waitForTimeout(500);
    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-C8-section-table.png'),
      fullPage: false,
    });
  });
});

// ── Group D: Audit Actions & API Calls ────────────────────────────────────────

test.describe('Stage 10 QA – D: Audit Actions & API Calls', () => {
  test('D1: Audit All Sections sends POST with empty body', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/audit/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });

    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.locator('button', { hasText: 'Audit All Sections' }).click();
    await page.waitForTimeout(500);

    expect(capturedBody).toBeDefined();
    expect(capturedBody.sectionId).toBeUndefined();
  });

  test('D2: Audit Section dropdown opens on click', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    await expect(dropdownMenu).not.toBeVisible();

    await page.locator('button', { hasText: 'Audit Section ▾' }).click();
    await page.waitForTimeout(300);
    await expect(dropdownMenu).toBeVisible();
  });

  test('D3: dropdown shows all section labels as options', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.locator('button', { hasText: 'Audit Section ▾' }).click();
    await page.waitForTimeout(300);

    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    await expect(dropdownMenu.locator('button', { hasText: 'Cold Open' })).toBeVisible();
    await expect(dropdownMenu.locator('button', { hasText: 'Part 1: Economics' })).toBeVisible();
    await expect(dropdownMenu.locator('button', { hasText: 'Part 2: Paradigm Shift' })).toBeVisible();
    await expect(dropdownMenu.locator('button', { hasText: 'Part 3: Mold' })).toBeVisible();
    await expect(dropdownMenu.locator('button')).toHaveCount(4);
  });

  test('D4: dropdown closes on outside click', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.locator('button', { hasText: 'Audit Section ▾' }).click();
    await page.waitForTimeout(300);

    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    await expect(dropdownMenu).toBeVisible();

    // Click outside — on heading
    await page.locator('h2', { hasText: 'Audit Results' }).click();
    await page.waitForTimeout(300);
    await expect(dropdownMenu).not.toBeVisible();
  });

  test('D5: dropdown item click sends POST with { sectionId }', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/audit/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });

    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.locator('button', { hasText: 'Audit Section ▾' }).click();
    await page.waitForTimeout(300);

    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    await dropdownMenu.locator('button', { hasText: 'Cold Open' }).click();
    await page.waitForTimeout(500);

    expect(capturedBody).not.toBeNull();
    expect(capturedBody.sectionId).toBe('cold_open');
  });

  test('D6: per-row ↺ Audit sends POST with { sectionId }', async ({ page }) => {
    let capturedBody: any = null;
    await page.route('**/api/pipeline/audit/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });

    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    // Click ↺ Audit on the first row (Cold Open)
    await page.locator('button', { hasText: '↺ Audit' }).first().click();
    await page.waitForTimeout(500);

    expect(capturedBody).not.toBeNull();
    expect(capturedBody.sectionId).toBe('cold_open');
  });

  test('D7: View Report toggles expanded state', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    // Initially no verdict column headers visible
    await expect(page.locator('.text-xs.font-semibold', { hasText: 'Verdict' })).not.toBeVisible();

    // Click View Report on first section
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(300);
    await expect(page.locator('.text-xs.font-semibold', { hasText: 'Verdict' })).toBeVisible();

    // Click again to collapse
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(300);
    await expect(page.locator('.text-xs.font-semibold', { hasText: 'Verdict' })).not.toBeVisible();
  });

  test('D8: multiple sections can be expanded simultaneously', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    // Expand first section (Cold Open) and last section (Part 3: Mold)
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(300);
    await page.locator('button', { hasText: 'View Report' }).last().click();
    await page.waitForTimeout(300);

    // Both should show spec detail areas — we should see verdict headers from both
    const verdictHeaders = page.locator('.text-xs.font-semibold', { hasText: 'Verdict' });
    expect(await verdictHeaders.count()).toBe(2);
  });

  test('D9: screenshot — dropdown open with section options', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.locator('button', { hasText: 'Audit Section ▾' }).click();
    await page.waitForTimeout(500);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-D9-dropdown-open.png'),
      fullPage: false,
    });
  });
});

// ── Group E: Frame Modal & Spec Viewer ────────────────────────────────────────

test.describe('Stage 10 QA – E: Frame Modal & Spec Viewer', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);
    // Expand Cold Open to access FAIL spec buttons
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);
  });

  test('E1: View Frame opens dialog with "Audit Frame" header', async ({ page }) => {
    await page.locator('button', { hasText: 'View Frame' }).first().click();
    await page.waitForTimeout(500);

    await expect(page.locator('dialog span', { hasText: 'Audit Frame' })).toBeVisible();
  });

  test('E2: dialog contains img with correct audit frame src', async ({ page }) => {
    await page.locator('button', { hasText: 'View Frame' }).first().click();
    await page.waitForTimeout(500);

    const img = page.locator('dialog img');
    await expect(img).toBeAttached();
    const src = await img.getAttribute('src');
    expect(src).toBe('/api/video/outputs/audit/cold_open/text_readable_frame.png');
  });

  test('E3: dialog close button ✕ closes dialog', async ({ page }) => {
    await page.locator('button', { hasText: 'View Frame' }).first().click();
    await page.waitForTimeout(500);
    await expect(page.locator('dialog span', { hasText: 'Audit Frame' })).toBeVisible();

    // Click the ✕ close button
    await page.locator('dialog button', { hasText: '✕' }).click();
    await page.waitForTimeout(300);

    // Dialog should be closed (not visible)
    await expect(page.locator('dialog span', { hasText: 'Audit Frame' })).not.toBeVisible();
  });

  test('E4: View Spec toggles inline pre element', async ({ page }) => {
    // Mock spec file fetch
    await page.route('**/api/pipeline/specs/file**', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: 'name: text_readable\nthreshold: 12px' }),
      }),
    );

    // No <pre> initially
    await expect(page.locator('pre')).not.toBeVisible();

    // Click View Spec
    await page.locator('button', { hasText: 'View Spec' }).first().click();
    await page.waitForTimeout(500);

    // <pre> should appear
    await expect(page.locator('pre').first()).toBeVisible();

    // Click View Spec again to close
    await page.locator('button', { hasText: 'View Spec' }).first().click();
    await page.waitForTimeout(300);
    await expect(page.locator('pre')).not.toBeVisible();
  });

  test('E5: spec viewer shows "Loading spec..." while fetching', async ({ page }) => {
    // Use a delayed route to catch the loading state
    await page.route('**/api/pipeline/specs/file**', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: 'name: text_readable' }),
      });
    });

    await page.locator('button', { hasText: 'View Spec' }).first().click();

    // Should show loading text
    await expect(page.locator('pre', { hasText: 'Loading spec...' })).toBeVisible({ timeout: 2000 });
  });

  test('E6: spec viewer shows fetched content after load', async ({ page }) => {
    await page.route('**/api/pipeline/specs/file**', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: 'name: text_readable\nthreshold: 12px' }),
      }),
    );

    await page.locator('button', { hasText: 'View Spec' }).first().click();
    await page.waitForTimeout(1000);

    await expect(page.locator('pre', { hasText: 'name: text_readable' })).toBeVisible();
    await expect(page.locator('pre', { hasText: 'threshold: 12px' })).toBeVisible();
  });

  test('E7: spec viewer shows error on fetch failure', async ({ page }) => {
    await page.route('**/api/pipeline/specs/file**', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"not found"}' }),
    );

    await page.locator('button', { hasText: 'View Spec' }).first().click();
    await page.waitForTimeout(1000);

    await expect(page.locator('pre', { hasText: 'Failed to load spec file.' })).toBeVisible();
  });

  test('E8: screenshot — frame modal open with image', async ({ page }) => {
    await page.locator('button', { hasText: 'View Frame' }).first().click();
    await page.waitForTimeout(500);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-E8-frame-modal.png'),
      fullPage: false,
    });
  });
});

// ── Group F: Create Annotation & Tab Navigation ──────────────────────────────

test.describe('Stage 10 QA – F: Create Annotation & Tab Navigation', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);
  });

  test('F1: Create Annotation button only visible for FAIL specs', async ({ page }) => {
    // Expand Cold Open (has both PASS and FAIL)
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);

    const createButtons = page.locator('button', { hasText: 'Create Annotation →' });
    // Only 1 FAIL spec in cold_open
    await expect(createButtons).toHaveCount(1);
  });

  test('F2: Create Annotation button NOT visible for PASS specs', async ({ page }) => {
    // Expand Cold Open — 3 PASS specs should have no action buttons
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);

    // Total Create Annotation buttons should match FAIL count (1)
    const createButtons = page.locator('button', { hasText: 'Create Annotation →' });
    await expect(createButtons).toHaveCount(1);

    // Verify that the button is NOT inside a PASS verdict row
    // View Frame buttons also only 1 (for the FAIL)
    const viewFrameButtons = page.locator('button', { hasText: 'View Frame' });
    await expect(viewFrameButtons).toHaveCount(1);
  });

  test('F3: clicking Create Annotation triggers callback (no crash)', async ({ page }) => {
    // Expand Cold Open
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);

    // Click Create Annotation — should not cause any JS errors
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.locator('button', { hasText: 'Create Annotation →' }).first().click();
    await page.waitForTimeout(500);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension'),
    );
    expect(appErrors).toHaveLength(0);
  });

  test('F4: View Frame / View Spec / Create Annotation all absent for PASS specs', async ({ page }) => {
    // Create a section with only PASS specs
    const passOnlySection = [
      {
        sectionId: 'pass_only',
        sectionLabel: 'All Passing',
        passCount: 2,
        failCount: 0,
        status: 'done',
        specs: [
          { specName: 'spec_a', verdict: 'PASS', summary: 'All good' },
          { specName: 'spec_b', verdict: 'PASS', summary: 'Perfect' },
        ],
      },
    ];

    // Re-navigate with pass-only data
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: passOnlySection }),
      }),
    );
    await navigateToStage10(page);

    // Expand
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);

    await expect(page.locator('button', { hasText: 'View Frame' })).toHaveCount(0);
    await expect(page.locator('button', { hasText: 'View Spec' })).toHaveCount(0);
    await expect(page.locator('button', { hasText: 'Create Annotation →' })).toHaveCount(0);
  });

  test('F5: expanded FAIL section shows all three action buttons', async ({ page }) => {
    // Expand Part 3: Mold (2 FAIL specs)
    await page.locator('button', { hasText: 'View Report' }).last().click();
    await page.waitForTimeout(500);

    // Should have 2 of each action button
    await expect(page.locator('button', { hasText: 'View Frame' })).toHaveCount(2);
    await expect(page.locator('button', { hasText: 'View Spec' })).toHaveCount(2);
    await expect(page.locator('button', { hasText: 'Create Annotation →' })).toHaveCount(2);
  });

  test('F6: screenshot — FAIL spec with all action buttons visible', async ({ page }) => {
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-F6-fail-actions.png'),
      fullPage: false,
    });
  });
});

// ── Group G: Error States & Network Failures ─────────────────────────────────

test.describe('Stage 10 QA – G: Error States & Network Failures', () => {
  test('G1: results API 500 shows error message', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"server error"}' }),
    );
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    const errorDiv = page.locator('div', { hasText: 'Failed to load audit results.' });
    await expect(errorDiv.first()).toBeVisible({ timeout: 10000 });
  });

  test('G2: error div has correct styling classes', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"server error"}' }),
    );
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    const errorDiv = page.locator('.bg-red-900\\/30.border.border-red-500\\/30.rounded.text-red-300');
    await expect(errorDiv).toBeVisible({ timeout: 10000 });
  });

  test('G3: audit run POST 500 does not crash', async ({ page }) => {
    await page.route('**/api/pipeline/audit/run', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"fail"}' }),
    );

    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.locator('button', { hasText: 'Audit All Sections' }).click();
    await page.waitForTimeout(1000);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension'),
    );
    expect(appErrors).toHaveLength(0);
  });

  test('G4: audit run POST abort does not crash', async ({ page }) => {
    await page.route('**/api/pipeline/audit/run', (route) => route.abort());

    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.locator('button', { hasText: 'Audit All Sections' }).click();
    await page.waitForTimeout(1000);

    // The fire-and-forget fetch might cause an unhandled rejection
    // Check that there's no "TypeError" / "Runtime" level crash
    const crashErrors = errors.filter(
      (e) => e.includes('TypeError') || e.includes('Runtime'),
    );
    expect(crashErrors).toHaveLength(0);
  });

  test('G5: spec file fetch 500 shows error in pre', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    await page.route('**/api/pipeline/specs/file**', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"not found"}' }),
    );

    // Expand Cold Open
    await page.locator('button', { hasText: 'View Report' }).first().click();
    await page.waitForTimeout(500);

    // Click View Spec on FAIL row
    await page.locator('button', { hasText: 'View Spec' }).first().click();
    await page.waitForTimeout(1000);

    await expect(page.locator('pre', { hasText: 'Failed to load spec file.' })).toBeVisible();
  });

  test('G6: empty sections shows empty state message', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      }),
    );
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    await expect(page.locator('div', { hasText: 'No audit results available.' }).first()).toBeVisible({
      timeout: 10000,
    });
  });

  test('G7: empty state has text-white/60 class', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      }),
    );
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    const emptyDiv = page.locator('.text-white\\/60', { hasText: 'No audit results available.' });
    await expect(emptyDiv).toBeVisible({ timeout: 10000 });
  });

  test('G8: screenshot — error state', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"server error"}' }),
    );
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);
    await page.waitForTimeout(1000);

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-G8-error-state.png'),
      fullPage: false,
    });
  });
});

// ── Group H: Loading & Edge Cases ────────────────────────────────────────────

test.describe('Stage 10 QA – H: Loading & Edge Cases', () => {
  test('H1: loading skeleton visible during slow results fetch', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS }),
      });
    });
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    // The skeleton should show animate-pulse
    const skeleton = page.locator('.animate-pulse');
    await expect(skeleton).toBeVisible({ timeout: 5000 });
  });

  test('H2: loading skeleton has bg-white/10 rounded children', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS }),
      });
    });
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    const skeleton = page.locator('.animate-pulse');
    await expect(skeleton).toBeVisible({ timeout: 5000 });

    const children = skeleton.locator('.bg-white\\/10.rounded');
    expect(await children.count()).toBe(3);
  });

  test('H3: empty state when sections is empty array', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      }),
    );
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    await expect(
      page.locator('div', { hasText: 'No audit results available.' }).first(),
    ).toBeVisible({ timeout: 10000 });
  });

  test('H4: section with 0 pass and 0 fail counts renders correctly', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    // Part 1 has passCount=0, failCount=0
    const part1Row = page.locator('.grid.grid-cols-6.items-center', { hasText: 'Part 1: Economics' });
    await expect(part1Row).toBeVisible();
    // The row should contain "0" (for both pass and fail)
    await expect(part1Row).toContainText('0');
  });

  test('H5: SSE audit-section event updates section counts in real time', async ({ page }) => {
    // Set up mocked results first
    await page.route('**/api/pipeline/audit/results', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS }),
      }),
    );

    // Set up SSE that sends an update after a delay
    await page.route('**/api/pipeline/audit/stream', (route) => {
      const body = `data: ${JSON.stringify({ type: 'connected' })}\n\ndata: ${JSON.stringify({ type: 'audit-section', sectionId: 'part1', passCount: 5, failCount: 1 })}\n\n`;
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body,
      });
    });

    await navigateToStage10(page);
    await page.waitForTimeout(2000);

    // Part 1 should now show updated counts
    const part1Row = page.locator('.grid.grid-cols-6.items-center', { hasText: 'Part 1: Economics' });
    await expect(part1Row).toContainText('5');
  });

  test('H6: section with no specs — expanded view shows empty detail area', async ({ page }) => {
    await navigateWithMockedResults(page, ALL_STATUS_SECTIONS);

    // Part 1 has empty specs array — expand it
    // Part 1 is the 2nd section (index 1)
    await page.locator('button', { hasText: 'View Report' }).nth(1).click();
    await page.waitForTimeout(500);

    // The expanded area should exist but have no spec rows — only the header row
    // Check that verdict/spec/summary headers appear but no verdict badges
    const detailArea = page.locator('.bg-white\\/5.border-t.border-white\\/10');
    await expect(detailArea.first()).toBeVisible();
  });

  test('H7: screenshot — loading skeleton state', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await new Promise((r) => setTimeout(r, 5000));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: ALL_STATUS_SECTIONS }),
      });
    });
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' }),
    );

    await navigateToStage10(page);

    await expect(page.locator('.animate-pulse')).toBeVisible({ timeout: 5000 });

    await page.screenshot({
      path: path.join(SCREENSHOT_DIR, 'stage10-H7-loading-skeleton.png'),
      fullPage: false,
    });
  });
});
