import { test, expect } from '@playwright/test';
import { buildMockAuditResults, loadActiveProjectFixture } from './helpers/project-fixtures';

const ACTIVE_PROJECT = loadActiveProjectFixture();
const PROJECT_SECTIONS = ACTIVE_PROJECT.sections;

function sectionRow(
  page: import('@playwright/test').Page,
  label: string,
) {
  return page.getByText(label, { exact: true }).locator('..');
}

test.describe('Stage 10: Audit', () => {
  test.beforeEach(async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(buildMockAuditResults()),
      });
    });
    await page.route('**/api/pipeline/audit/stream', (route) =>
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' })
    );

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Audit stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    // Wait for audit results to load (section rows appear or empty state)
    await expect(
      page.locator('h2', { hasText: 'Audit Results' })
    ).toBeVisible({ timeout: 15000 });
    // Wait for loading to finish
    await page.waitForTimeout(1000);
  });

  test('renders without crash', async ({ page }) => {
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays stage heading', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible();
  });

  test('heading text is readable on dark background (dark theme fix)', async ({ page }) => {
    const h2 = page.locator('h2', { hasText: 'Audit Results' });
    await expect(h2).toBeVisible();

    const isLight = await h2.evaluate((el) => {
      const color = getComputedStyle(el).color;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = color;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r > 200 && g > 200 && b > 200;
    });
    expect(isLight).toBe(true);
  });

  test('displays "Audit All Sections" button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Audit All Sections' })).toBeVisible();
  });

  test('displays "Audit Section" dropdown', async ({ page }) => {
    // It's a <button> not a <summary>
    await expect(page.locator('button', { hasText: 'Audit Section' })).toBeVisible();
  });

  test('section rows are present for the active project', async ({ page }) => {
    // Wait for sections to load from API
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const viewReportButtons = page.locator('button', { hasText: 'View Report' });
    await expect(viewReportButtons).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('section labels are visible in table', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    for (const section of PROJECT_SECTIONS) {
      await expect(sectionRow(page, section.label)).toBeVisible();
    }
  });

  test('section label text is readable on dark background (dark theme fix)', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const firstRow = sectionRow(page, PROJECT_SECTIONS[0]?.label ?? 'Animation Section');
    await expect(firstRow).toBeVisible();

    const isLight = await firstRow.evaluate((el) => {
      const color = getComputedStyle(el).color;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = color;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r > 180 && g > 180 && b > 180;
    });
    expect(isLight).toBe(true);
  });

  test('table column headers are present', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    await expect(page.getByText('Section').first()).toBeVisible();
    await expect(page.getByText('Pass').first()).toBeVisible();
    await expect(page.getByText('Fail').first()).toBeVisible();
    await expect(page.getByText('Status').first()).toBeVisible();
    await expect(page.getByText('Actions').first()).toBeVisible();
  });

  test('status badges are visible with readable text (dark theme fix)', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    // The status badges should show "done", "pending", or other statuses
    const statusBadge = page.locator('span', { hasText: /^(done|pending|running|error)$/ }).first();
    await expect(statusBadge).toBeVisible();

    const isReadable = await statusBadge.evaluate((el) => {
      const color = getComputedStyle(el).color;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = color;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r > 130 || g > 130 || b > 130;
    });
    expect(isReadable).toBe(true);
  });

  test('each section has a "View Report" button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const buttons = page.locator('button', { hasText: 'View Report' });
    await expect(buttons).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('each section has an "Audit" re-run button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const auditButtons = page.locator('button', { hasText: '↺ Audit' });
    await expect(auditButtons).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('"View Report" button text is readable (dark theme fix)', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const btn = page.locator('button', { hasText: 'View Report' }).first();

    const isReadable = await btn.evaluate((el) => {
      const color = getComputedStyle(el).color;
      // Handle oklch, rgb, and other color formats by painting to canvas
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = color;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      // Blue link text: blue channel should be prominent
      return b > 100 && (r + g + b) > 100;
    });
    expect(isReadable).toBe(true);
  });

  test('no console errors on load', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(2000);
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Audit All Sections button click triggers audit API call', async ({ page }) => {
    let auditCalled = false;
    let capturedBody: any = null;
    await page.route('**/api/pipeline/audit/run', async (route) => {
      auditCalled = true;
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    const auditAllButton = page.locator('button', { hasText: 'Audit All Sections' });
    await auditAllButton.click();
    await page.waitForTimeout(1000);

    expect(auditCalled).toBe(true);
    // When auditing all sections, the body should NOT contain a specific sectionId
    expect(capturedBody).toBeDefined();
    expect(capturedBody.sectionId).toBeUndefined();
  });

  test('Audit Section dropdown opens with section list', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });

    // The dropdown menu should not be visible initially
    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    await expect(dropdownMenu).not.toBeVisible();

    // Click the "Audit Section" dropdown button
    const dropdownButton = page.locator('button', { hasText: 'Audit Section' });
    await dropdownButton.click();
    await page.waitForTimeout(500);

    // The dropdown menu should now be visible
    await expect(dropdownMenu).toBeVisible();

    // It should contain buttons for each section
    const dropdownItems = dropdownMenu.locator('button');
    const count = await dropdownItems.count();
    expect(count).toBe(PROJECT_SECTIONS.length);
  });

  test('Audit Section dropdown closes on outside click', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });

    // Open the dropdown
    const dropdownButton = page.locator('button', { hasText: 'Audit Section' });
    await dropdownButton.click();
    await page.waitForTimeout(500);

    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    await expect(dropdownMenu).toBeVisible();

    // Click outside the dropdown (on the heading area)
    await page.locator('h2', { hasText: 'Audit Results' }).click();
    await page.waitForTimeout(500);

    // The dropdown should be closed
    await expect(dropdownMenu).not.toBeVisible();
  });

  test('Audit Section dropdown item triggers section audit', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });

    let capturedBody: any = null;
    await page.route('**/api/pipeline/audit/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    // Open the dropdown
    const dropdownButton = page.locator('button', { hasText: 'Audit Section' });
    await dropdownButton.click();
    await page.waitForTimeout(500);

    // Click the first item in the dropdown
    const dropdownMenu = page.locator('.absolute.right-0.mt-2.bg-gray-800');
    const firstItem = dropdownMenu.locator('button').first();
    await firstItem.click();
    await page.waitForTimeout(1000);

    // The API should have been called with a specific section target
    expect(capturedBody).not.toBeNull();
    expect(Array.isArray(capturedBody.sections)).toBe(true);
    expect(capturedBody.sections).toHaveLength(1);
    expect(typeof capturedBody.sections[0]).toBe('string');

    // The dropdown should be closed after selection
    await expect(dropdownMenu).not.toBeVisible();
  });

  test('View Report button expands section details', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });

    // The expanded detail area should not be visible initially
    // Detail area contains "Verdict", "Spec", "Summary" sub-headers
    const detailArea = page.locator('text=Verdict').first();
    await expect(detailArea).not.toBeVisible();

    // Click the first "View Report" button
    const firstViewReport = page.locator('button', { hasText: 'View Report' }).first();
    await firstViewReport.click();
    await page.waitForTimeout(500);

    // The expanded section with Verdict/Spec/Summary headers should now be visible
    await expect(page.locator('.text-xs.font-semibold', { hasText: 'Verdict' }).first()).toBeVisible();
    await expect(page.locator('.text-xs.font-semibold', { hasText: 'Spec' }).first()).toBeVisible();
    await expect(page.locator('.text-xs.font-semibold', { hasText: 'Summary' }).first()).toBeVisible();
  });

  test('Re-audit button triggers section re-audit', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });

    let capturedBody: any = null;
    await page.route('**/api/pipeline/audit/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    // Click the first re-audit button
    const firstReauditButton = page.locator('button', { hasText: '↺ Audit' }).first();
    await firstReauditButton.click();
    await page.waitForTimeout(1000);

    // The API should have been called with the specific section target
    expect(capturedBody).not.toBeNull();
    expect(Array.isArray(capturedBody.sections)).toBe(true);
    expect(capturedBody.sections).toHaveLength(1);
    expect(typeof capturedBody.sections[0]).toBe('string');
  });

  test('Play Video swaps the frame preview into an inline section video', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              sectionId: 'cold_open',
              sectionLabel: 'Cold Open',
              passCount: 1,
              failCount: 1,
              status: 'done',
              specs: [
                { specName: 'framing', verdict: 'PASS', summary: 'Looks good' },
                { specName: 'color_balance', verdict: 'FAIL', summary: 'Colors off', finding: 'Too dark', specPath: '/specs/color.yaml' },
              ],
            },
          ],
        }),
      });
    });

    // Mock SSE stream to prevent connection issues
    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    // Navigate to Audit stage with mocked data
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });
    await page.waitForTimeout(1000);

    // Expand the section
    const viewReportButton = page.locator('button', { hasText: 'View Report' }).first();
    await expect(viewReportButton).toBeVisible({ timeout: 10000 });
    await viewReportButton.click();
    await page.waitForTimeout(500);

    const playVideoButton = page.locator('button', { hasText: 'Play Video' }).first();
    await expect(playVideoButton).toBeVisible({ timeout: 5000 });
    await playVideoButton.click();
    await page.waitForTimeout(500);

    const inlineVideo = page.locator('video').first();
    await expect(inlineVideo).toBeVisible();
    await expect(page.locator('img[alt="color_balance audit frame"]')).toHaveCount(0);
    const src = await inlineVideo.getAttribute('src');
    expect(src).toBe('/api/video/outputs/sections/cold_open.mp4');
  });

  test('FAIL rows show inline spec content without clicking a view button', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              sectionId: 'cold_open',
              sectionLabel: 'Cold Open',
              passCount: 0,
              failCount: 1,
              status: 'done',
              specs: [
                { specName: 'color_balance', verdict: 'FAIL', summary: 'Colors off', finding: 'Too dark', specPath: '/specs/color.yaml' },
              ],
            },
          ],
        }),
      });
    });

    // Mock the spec file fetch
    await page.route('**/api/pipeline/specs/file**', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: 'name: color_balance\nthreshold: 0.8\ndescription: Check color balance' }),
      });
    });

    // Mock SSE stream
    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    // Navigate to Audit stage with mocked data
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });
    await page.waitForTimeout(1000);

    // Expand the section
    const viewReportButton = page.locator('button', { hasText: 'View Report' }).first();
    await expect(viewReportButton).toBeVisible({ timeout: 10000 });
    await viewReportButton.click();
    await page.waitForTimeout(500);

    await expect(page.getByText('Frame Preview')).toBeVisible();
    await expect(page.getByText('Spec Preview')).toBeVisible();
    await expect(page.getByText('name: color_balance')).toBeVisible({ timeout: 5000 });
  });

  test('FAIL rows show inline frame and spec preview beside the summary', async ({ page }) => {
    await page.route('**/api/pipeline/audit/results', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              sectionId: 'cold_open',
              sectionLabel: 'Cold Open',
              passCount: 0,
              failCount: 1,
              status: 'done',
              specs: [
                {
                  specName: 'color_balance',
                  verdict: 'FAIL',
                  summary: 'Colors off',
                  finding: 'Too dark',
                  specPath: '/specs/color.yaml',
                },
              ],
            },
          ],
        }),
      });
    });

    await page.route('**/api/pipeline/specs/file**', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          content: 'name: color_balance\nthreshold: 0.8\ndescription: Check color balance',
        }),
      });
    });

    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });
    await page.waitForTimeout(1000);

    await page.locator('button', { hasText: 'View Report' }).first().click();

    await expect(page.getByText('Frame Preview')).toBeVisible();
    await expect(page.getByText('Spec Preview')).toBeVisible();
    await expect(page.locator('img[alt=\"color_balance audit frame\"]')).toBeVisible();
    await expect(page.getByText('name: color_balance')).toBeVisible({ timeout: 5000 });
  });
});
