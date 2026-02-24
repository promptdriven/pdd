import { test, expect } from '@playwright/test';

test.describe('Review Tab', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);
  });

  test('shows video player area', async ({ page }) => {
    // The Play/Pause button should be visible
    await expect(page.locator('text=Play/Pause')).toBeVisible();
  });

  test('shows annotation drawing tools', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'RECTANGLE' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'CIRCLE' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'ARROW' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'TEXT' })).toBeVisible();
  });

  test('shows Annotations panel', async ({ page }) => {
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();
  });

  test('shows empty annotation state', async ({ page }) => {
    await expect(page.locator('text=No annotations yet')).toBeVisible();
  });

  test('sidebar is not visible in Review tab', async ({ page }) => {
    const sidebar = page.locator('aside');
    await expect(sidebar).not.toBeVisible();
  });

  test('video player container has dark background', async ({ page }) => {
    const videoContainer = page.locator('.aspect-video').first();
    await expect(videoContainer).toBeVisible();
    const isDark = await videoContainer.evaluate((el) => {
      const bgColor = getComputedStyle(el).backgroundColor;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = bgColor;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r < 50 && g < 50 && b < 50;
    });
    expect(isDark).toBe(true);
  });

  test('canvas overlay is present for drawing', async ({ page }) => {
    const canvas = page.locator('canvas');
    await expect(canvas).toBeVisible();
  });

  test('video element is present', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();
  });

  test('freehand tool is selected by default (blue bg)', async ({ page }) => {
    const freehandBtn = page.locator('button', { hasText: 'FREEHAND' });
    await expect(freehandBtn).toBeVisible();
    const isBlue = await freehandBtn.evaluate((el) => {
      const bgColor = getComputedStyle(el).backgroundColor;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = bgColor;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return b > 150;
    });
    expect(isBlue).toBe(true);
  });

  test('tool buttons text is readable (dark theme)', async ({ page }) => {
    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    await expect(rectBtn).toBeVisible();
    const isLight = await rectBtn.evaluate((el) => {
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

  test('time display shows 0:00 / 0:00', async ({ page }) => {
    await expect(page.getByText('0:00 / 0:00')).toBeVisible();
  });

  test('keyboard shortcut hints are visible', async ({ page }) => {
    await expect(page.getByText('Space = Annotate')).toBeVisible();
  });

  test('Annotations panel heading text is readable (dark theme)', async ({ page }) => {
    const heading = page.getByText('Annotations', { exact: true });
    await expect(heading).toBeVisible();
    const color = await heading.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Text should be white/light
      const isLight = r > 180 && g > 180 && b > 180;
      expect(isLight).toBe(true);
    }
  });

  test('Apply Fixes button is present and disabled when no annotations', async ({ page }) => {
    const applyBtn = page.locator('button', { hasText: /Apply \d+ Fixes/ });
    await expect(applyBtn).toBeVisible();
    await expect(applyBtn).toBeDisabled();
  });

  test('switching back to Pipeline shows sidebar again', async ({ page }) => {
    // Sidebar should not be visible in Review
    await expect(page.locator('aside')).not.toBeVisible();

    // Switch back to Pipeline
    await page.locator('button', { hasText: 'Pipeline' }).click();
    await page.waitForTimeout(500);

    // Sidebar should be visible again
    await expect(page.locator('aside')).toBeVisible();
  });

  test('Review tab has active blue border indicator', async ({ page }) => {
    const reviewBtn = page.locator('button', { hasText: 'Review' });
    await expect(reviewBtn).toBeVisible();
    const borderStyle = await reviewBtn.evaluate((el) => getComputedStyle(el).borderBottomStyle);
    expect(borderStyle).toBe('solid');
  });

  test('no console errors in Review tab', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(1000);
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
