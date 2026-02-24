import { test, expect } from '@playwright/test';

test.describe('Stage 9: Render & Stitch', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Render stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    // Wait for render status to load (table appears with Section ID column)
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });
  });

  test('renders without crash', async ({ page }) => {
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays stage heading', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
    await expect(page.locator('h2', { hasText: 'Render & Stitch' })).toBeVisible();
  });

  test('displays stage description', async ({ page }) => {
    await expect(page.locator('text=Render Remotion sections in parallel')).toBeVisible();
  });

  test('heading text is readable on dark background (dark theme fix)', async ({ page }) => {
    const h2 = page.locator('h2', { hasText: 'Stage 9' });
    await expect(h2).toBeVisible();

    const color = await h2.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Text should be light (white) on dark background
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(true);
    }
  });

  test('description text is readable on dark background (dark theme fix)', async ({ page }) => {
    const desc = page.locator('p', { hasText: 'Render Remotion sections in parallel' });
    await expect(desc).toBeVisible();

    const color = await desc.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Text should be at least medium brightness, not dark
      const isDark = r < 100 && g < 100 && b < 100;
      expect(isDark).toBe(false);
    }
  });

  test('displays render mode selector with All/Missing/Selected options', async ({ page }) => {
    const select = page.locator('select');
    await expect(select).toBeVisible();

    // Check options
    const options = select.locator('option');
    await expect(options).toHaveCount(3);
    await expect(options.nth(0)).toHaveText('All');
    await expect(options.nth(1)).toHaveText('Missing');
    await expect(options.nth(2)).toHaveText('Selected');
  });

  test('render mode selector text is readable (dark theme fix)', async ({ page }) => {
    const select = page.locator('select');
    await expect(select).toBeVisible();

    const color = await select.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Text should be dark (on white bg select)
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('render mode selector is changeable', async ({ page }) => {
    const select = page.locator('select');
    await select.selectOption('missing');
    await expect(select).toHaveValue('missing');
    await select.selectOption('selected');
    await expect(select).toHaveValue('selected');
    await select.selectOption('all');
    await expect(select).toHaveValue('all');
  });

  test('displays Render button', async ({ page }) => {
    await expect(page.locator('button', { hasText: /Render/ }).first()).toBeVisible();
  });

  test('displays Stitch Full Video button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Stitch Full Video' })).toBeVisible();
  });

  test('displays Section Renders heading', async ({ page }) => {
    await expect(page.locator('h3', { hasText: 'Section Renders' })).toBeVisible();
  });

  test('displays section renders table headers', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Select' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Duration' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Status' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Progress' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Preview' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Re-render' })).toBeVisible();
  });

  test('table headers are readable on light background (dark theme fix)', async ({ page }) => {
    const thSelect = page.locator('th', { hasText: 'Select' });
    await expect(thSelect).toBeVisible();

    const color = await thSelect.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Text should be dark on the light bg-slate-50 background
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('section renders table shows all 7 project sections', async ({ page }) => {
    const rows = page.locator('tbody tr');
    await expect(rows).toHaveCount(7);
  });

  test('section IDs are visible in table (dark theme fix)', async ({ page }) => {
    // After fix, section IDs should use explicit dark text color
    const firstSectionCell = page.locator('tbody tr').first().locator('td').nth(1);
    await expect(firstSectionCell).toBeVisible();
    await expect(firstSectionCell).toContainText('cold_open');

    const color = await firstSectionCell.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Text should be dark on white background
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('duration values are visible in table (dark theme fix)', async ({ page }) => {
    const firstDurationCell = page.locator('tbody tr').first().locator('td').nth(2);
    await expect(firstDurationCell).toBeVisible();
    await expect(firstDurationCell).toContainText('0.00');

    const color = await firstDurationCell.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('each row has a selection checkbox', async ({ page }) => {
    const checkboxes = page.locator('tbody tr input[type="checkbox"]');
    await expect(checkboxes).toHaveCount(7);
  });

  test('checkboxes are toggleable', async ({ page }) => {
    const firstCheckbox = page.locator('tbody tr').first().locator('input[type="checkbox"]');
    await expect(firstCheckbox).not.toBeChecked();
    await firstCheckbox.check();
    await expect(firstCheckbox).toBeChecked();
    await firstCheckbox.uncheck();
    await expect(firstCheckbox).not.toBeChecked();
  });

  test('each row has a preview button', async ({ page }) => {
    const previewButtons = page.locator('tbody tr button[title="Preview"]');
    await expect(previewButtons).toHaveCount(7);
  });

  test('each row has a re-render button', async ({ page }) => {
    const rerenderButtons = page.locator('tbody tr button[title="Re-render"]');
    await expect(rerenderButtons).toHaveCount(7);
  });

  test('all sections show Missing status', async ({ page }) => {
    // Wait for rows to be present
    await expect(page.locator('tbody tr')).toHaveCount(7);
    const missingBadges = page.locator('tbody').locator('span', { hasText: 'Missing' });
    await expect(missingBadges).toHaveCount(7);
  });

  test('all sections show 0% progress', async ({ page }) => {
    await expect(page.locator('tbody tr')).toHaveCount(7);
    const progressTexts = page.locator('tbody .text-xs.text-slate-500', { hasText: '0%' });
    await expect(progressTexts).toHaveCount(7);
  });

  test('no console errors on load', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(2000);
    const sidebar = page.locator('aside');
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
