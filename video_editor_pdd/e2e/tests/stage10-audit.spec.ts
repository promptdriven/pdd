import { test, expect } from '@playwright/test';

test.describe('Stage 10: Audit', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Audit stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div').filter({ hasText: /^10\s*Audit/ }).click();
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
    await expect(page.locator('summary', { hasText: 'Audit Section' })).toBeVisible();
  });

  test('section rows are present (7 sections)', async ({ page }) => {
    // Wait for sections to load from API
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const viewReportButtons = page.locator('button', { hasText: 'View Report' });
    await expect(viewReportButtons).toHaveCount(7);
  });

  test('section labels are visible in table', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    // Use the section rows (grid rows next to View Report buttons) to verify labels
    // Each section label appears as a div sibling to the View Report button row
    await expect(page.getByText('Cold Open').first()).toBeVisible();
    await expect(page.getByText('Part 1: Economics').first()).toBeVisible();
    await expect(page.getByText('Closing').first()).toBeVisible();
  });

  test('section label text is readable on dark background (dark theme fix)', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    // Find the section label in the table row (not the dropdown button)
    // The grid row div contains the section label text
    const sectionLabel = page.getByText('Part 1: Economics').first();
    await expect(sectionLabel).toBeVisible();

    const isLight = await sectionLabel.evaluate((el) => {
      const color = getComputedStyle(el).color;
      // Handle oklch, rgb, and other color formats
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
    await expect(buttons).toHaveCount(7);
  });

  test('each section has an "Audit" re-run button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'View Report' }).first()).toBeVisible({ timeout: 10000 });
    const auditButtons = page.locator('button', { hasText: '↺ Audit' });
    await expect(auditButtons).toHaveCount(7);
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
    await sidebar.locator('div').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
