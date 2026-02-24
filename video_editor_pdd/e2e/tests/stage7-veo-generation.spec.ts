import { test, expect } from '@playwright/test';

test.describe('Stage 7: Veo Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Veo Gen stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    // Wait for clip data to load (loading state disappears, table appears)
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });
  });

  test('renders without crash', async ({ page }) => {
    // No runtime error overlay should appear
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays Character References section', async ({ page }) => {
    const heading = page.locator('h3', { hasText: 'Character References' });
    await expect(heading).toBeVisible();
  });

  test('displays character reference with label', async ({ page }) => {
    // The project has one reference: "Alex (protagonist)"
    await expect(page.locator('text=Alex (protagonist)').first()).toBeVisible();
  });

  test('displays reference Regenerate button', async ({ page }) => {
    // There should be a Regenerate button near the reference
    const refRegenBtn = page.locator('button', { hasText: 'Regenerate' }).first();
    await expect(refRegenBtn).toBeVisible();
  });

  test('displays Frame Chaining section', async ({ page }) => {
    const heading = page.locator('h3', { hasText: 'Frame Chaining' });
    await expect(heading).toBeVisible();
  });

  test('displays frame chain dependencies', async ({ page }) => {
    // Frame chaining should show dependency arrows like "outputs/veo/cold_open_last_frame.png -> part1_economics"
    await expect(page.locator('text=cold_open').first()).toBeVisible();
    await expect(page.locator('text=part1_economics').first()).toBeVisible();
  });

  test('displays Generate All button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate All' })).toBeVisible();
  });

  test('displays Generate Missing button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate Missing' })).toBeVisible();
  });

  test('displays Generate Section button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate Section' })).toBeVisible();
  });

  test('displays section dropdown', async ({ page }) => {
    const select = page.locator('select');
    await expect(select).toBeVisible();
  });

  test('displays auto-composite checkbox with label', async ({ page }) => {
    await expect(page.locator('text=Auto-composite split-screen')).toBeVisible();
    const checkbox = page.locator('input[type="checkbox"]');
    await expect(checkbox).toBeVisible();
  });

  test('auto-composite checkbox is toggleable', async ({ page }) => {
    const checkbox = page.locator('input[type="checkbox"]');
    await expect(checkbox).not.toBeChecked();
    await checkbox.check();
    await expect(checkbox).toBeChecked();
    await checkbox.uncheck();
    await expect(checkbox).not.toBeChecked();
  });

  test('clip table headers are visible', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Section' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Aspect' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Status' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Actions' }).first()).toBeVisible();
  });

  test('clip table shows all project sections as rows', async ({ page }) => {
    // 7 sections in project.json -> 7 clip rows
    const rows = page.locator('tbody tr');
    await expect(rows).toHaveCount(7);
  });

  test('clip table text is readable (dark theme fix)', async ({ page }) => {
    // Bug fix: clip ID, section, and aspect text was white-on-white in dark theme.
    // After fix, they should have explicit dark text color.
    const firstClipCell = page.locator('tbody tr').first().locator('td').first();
    await expect(firstClipCell).toBeVisible();

    const color = await firstClipCell.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Dark text: RGB values should NOT all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('all clips show missing status', async ({ page }) => {
    // No Veo clips have been generated yet
    const missingBadges = page.locator('text=missing');
    const count = await missingBadges.count();
    expect(count).toBeGreaterThanOrEqual(7);
  });

  test('clip aspect ratio is 16:9', async ({ page }) => {
    // All clips should show 16:9 from project.json defaultAspectRatio
    await expect(page.locator('td', { hasText: '16:9' }).first()).toBeVisible();
  });

  test('displays Clip Events section', async ({ page }) => {
    await expect(page.locator('h3', { hasText: 'Clip Events' })).toBeVisible();
  });

  test('displays Continue button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Continue' })).toBeVisible();
  });

  test('auto-composite label has readable text (dark theme fix)', async ({ page }) => {
    // Bug fix: "Auto-composite split-screen" text was invisible in dark theme.
    const label = page.locator('text=Auto-composite split-screen');
    await expect(label).toBeVisible();

    const color = await label.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('no console errors on load', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(2000);
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(2000);
    // Filter out non-application errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
