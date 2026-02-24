import { test, expect } from '@playwright/test';

test.describe('Stage 8: Composition Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Compositions stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    // Wait for the composition data to load (loading text disappears, sections appear)
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });
  });

  test('renders without crash', async ({ page }) => {
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays stage heading and description', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
    await expect(page.locator('text=Generate Remotion compositions')).toBeVisible();
  });

  test('displays Components heading with count', async ({ page }) => {
    const heading = page.locator('h3', { hasText: /Components\s*\(\d+\)/ });
    await expect(heading).toBeVisible();
  });

  test('displays Generate All Compositions button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate All Compositions' })).toBeVisible();
  });

  test('displays section accordions for all project sections', async ({ page }) => {
    // Project has 7 sections - each should be visible as a collapsible section
    await expect(page.locator('button', { hasText: 'Cold Open' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Part 1: Economics' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Part 2: Paradigm Shift' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Part 3: The Mold' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Part 4: Precision Tradeoff' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Part 5: Compound Returns' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Closing' }).first()).toBeVisible();
  });

  test('section accordions are togglable', async ({ page }) => {
    // Initially sections show "Hide"
    const coldOpenBtn = page.locator('button', { hasText: 'Cold Open' });
    await expect(coldOpenBtn).toBeVisible();

    // The Hide/Show text should be visible
    const hideShow = coldOpenBtn.locator('span', { hasText: /Hide|Show/ });
    await expect(hideShow).toBeVisible();

    // Click to collapse
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Show' })).toBeVisible();

    // Click to expand again
    await coldOpenBtn.click();
    await expect(coldOpenBtn.locator('span', { hasText: 'Hide' })).toBeVisible();
  });

  test('displays Section Wrappers heading', async ({ page }) => {
    await expect(page.locator('h4', { hasText: 'Section Wrappers' })).toBeVisible();
  });

  test('displays Asset Staging Manifest heading', async ({ page }) => {
    await expect(page.locator('h3', { hasText: 'Asset Staging Manifest' })).toBeVisible();
  });

  test('displays Stage All Missing button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Stage All Missing' })).toBeVisible();
  });

  test('displays staging manifest table headers', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Filename' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Expected' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Present' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Action' }).first()).toBeVisible();
  });

  test('displays Job Logs toggle', async ({ page }) => {
    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn).toBeVisible();

    // Toggle open
    await jobLogsBtn.click();
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();

    // Toggle closed
    await jobLogsBtn.click();
    await expect(jobLogsBtn.locator('span', { hasText: 'Show' })).toBeVisible();
  });

  test('displays Continue button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Continue' })).toBeVisible();
  });

  test('heading text is readable on dark background', async ({ page }) => {
    const h2 = page.locator('h2', { hasText: 'Stage 8' });
    await expect(h2).toBeVisible();

    const color = await h2.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // White text: RGB values should all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(true);
    }
  });

  test('components panel text is readable on white background', async ({ page }) => {
    const h3 = page.locator('h3', { hasText: /Components/ });
    await expect(h3).toBeVisible();

    const color = await h3.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Dark text on white panel: RGB values should NOT all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('section accordion text is readable', async ({ page }) => {
    const sectionBtn = page.locator('button', { hasText: 'Cold Open' });
    await expect(sectionBtn).toBeVisible();

    const color = await sectionBtn.evaluate((el) => {
      const span = el.querySelector('span');
      return span ? getComputedStyle(span).color : getComputedStyle(el).color;
    });
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('staging manifest table headers are readable', async ({ page }) => {
    const filenameHeader = page.locator('th', { hasText: 'Filename' }).first();
    await expect(filenameHeader).toBeVisible();

    const color = await filenameHeader.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('wrapper status badges show Missing', async ({ page }) => {
    // Scroll down to see Section Wrappers
    const wrapperHeading = page.locator('h4', { hasText: 'Section Wrappers' });
    await wrapperHeading.scrollIntoViewIfNeeded();
    await expect(wrapperHeading).toBeVisible();
    // Wrappers are rendered below the section accordions with status badges
    const missingBadges = page.locator('span.rounded-full', { hasText: 'Missing' });
    await expect(missingBadges.first()).toBeVisible({ timeout: 5000 });
    const count = await missingBadges.count();
    expect(count).toBeGreaterThan(0);
  });

  test('no console errors on load', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(2000);
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
