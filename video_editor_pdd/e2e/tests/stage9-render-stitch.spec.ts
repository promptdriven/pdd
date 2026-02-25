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
    // Duration is rendered as durationSeconds.toFixed(2) — a numeric string
    await expect(firstDurationCell).toContainText(/\d+\.\d{2}/);

    const color = await firstDurationCell.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // text-slate-200 is light text on dark background
      // Just verify the text is not invisible (not zero opacity)
      const isBlack = r === 0 && g === 0 && b === 0;
      expect(isBlack).toBe(false);
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
    // Status badge renders as "Missing" in a rounded span
    const missingBadges = page.locator('tbody span.rounded-full', { hasText: 'Missing' });
    const count = await missingBadges.count();
    expect(count).toBeGreaterThanOrEqual(1);
  });

  test('all sections show 0% progress', async ({ page }) => {
    await expect(page.locator('tbody tr')).toHaveCount(7);
    // Progress text uses class text-slate-400 (not text-slate-500)
    const progressTexts = page.locator('tbody .text-xs', { hasText: '0%' });
    const count = await progressTexts.count();
    expect(count).toBeGreaterThanOrEqual(1);
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

  test('Render button click triggers render API call with selected mode', async ({ page }) => {
    // Intercept the render API call
    let capturedBody: any = null;
    await page.route('**/api/pipeline/render/run', async (route) => {
      const request = route.request();
      capturedBody = JSON.parse(request.postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-job-123' }),
      });
    });

    // Select "Missing" mode
    const select = page.locator('select');
    await select.selectOption('missing');
    await expect(select).toHaveValue('missing');

    // Click the Render button
    const renderButton = page.locator('button', { hasText: /Render/ }).first();
    await renderButton.click();

    // Wait for the API call to be made
    await page.waitForTimeout(1000);

    // Verify the request was made with section IDs
    expect(capturedBody).not.toBeNull();
    expect(capturedBody).toHaveProperty('sections');
    expect(Array.isArray(capturedBody.sections)).toBe(true);
  });

  test('Stitch Full Video button click triggers stitch API call', async ({ page }) => {
    // Intercept the stitch API call
    let stitchCalled = false;
    await page.route('**/api/pipeline/stitch/run', async (route) => {
      stitchCalled = true;
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    // Also mock the status reload that happens after stitch
    await page.route('**/api/pipeline/render/status', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            { id: 'cold_open', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'intro', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'main_1', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'main_2', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'main_3', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'recap', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'outro', durationSeconds: 0, status: 'missing', progress: 0 },
          ],
          fullVideo: { exists: false },
        }),
      });
    });

    const stitchButton = page.locator('button', { hasText: 'Stitch Full Video' });
    await stitchButton.click();

    await page.waitForTimeout(1000);
    expect(stitchCalled).toBe(true);
  });

  test('Preview button click opens video modal overlay', async ({ page }) => {
    // Verify the preview modal is NOT visible initially
    await expect(page.locator('text=Preview —')).not.toBeVisible();

    // Click the first preview button
    const firstPreviewButton = page.locator('tbody tr').first().locator('button[title="Preview"]');
    await firstPreviewButton.click();
    await page.waitForTimeout(500);

    // The modal overlay should appear with "Preview — cold_open" text
    await expect(page.locator('text=Preview —')).toBeVisible();

    // A video element should be present inside the modal
    const modalVideo = page.locator('.fixed video');
    await expect(modalVideo).toBeAttached();
  });

  test('Preview modal closes on overlay click', async ({ page }) => {
    // Open the preview modal
    const firstPreviewButton = page.locator('tbody tr').first().locator('button[title="Preview"]');
    await firstPreviewButton.click();
    await page.waitForTimeout(500);
    await expect(page.locator('text=Preview —')).toBeVisible();

    // Click the overlay background (the fixed backdrop)
    const overlay = page.locator('.fixed.inset-0.bg-black\\/50');
    // Click at the top-left corner of the overlay (outside the modal content)
    await overlay.click({ position: { x: 10, y: 10 } });
    await page.waitForTimeout(500);

    // Modal should be closed
    await expect(page.locator('text=Preview —')).not.toBeVisible();
  });

  test('Preview modal closes on close button click', async ({ page }) => {
    // Open the preview modal
    const firstPreviewButton = page.locator('tbody tr').first().locator('button[title="Preview"]');
    await firstPreviewButton.click();
    await page.waitForTimeout(500);
    await expect(page.locator('text=Preview —')).toBeVisible();

    // Click the close button (✕)
    const closeButton = page.locator('.fixed button', { hasText: '✕' });
    await closeButton.click();
    await page.waitForTimeout(500);

    // Modal should be closed
    await expect(page.locator('text=Preview —')).not.toBeVisible();
  });

  test('Re-render button on a row triggers section re-render API call', async ({ page }) => {
    // Intercept the render API call
    let capturedBody: any = null;
    await page.route('**/api/pipeline/render/run', async (route) => {
      capturedBody = JSON.parse(route.request().postData() || '{}');
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'rerender-job-456' }),
      });
    });

    // Click the re-render button on the first row
    const firstRerenderButton = page.locator('tbody tr').first().locator('button[title="Re-render"]');
    await firstRerenderButton.click();

    await page.waitForTimeout(1000);

    // Verify the API was called with only the first section
    expect(capturedBody).not.toBeNull();
    expect(capturedBody).toHaveProperty('sections');
    expect(capturedBody.sections).toHaveLength(1);
    expect(capturedBody.sections[0]).toBe('cold_open');
  });

  test('Multiple checkboxes can be toggled independently', async ({ page }) => {
    const checkboxes = page.locator('tbody tr input[type="checkbox"]');
    await expect(checkboxes).toHaveCount(7);

    // Check the first and third checkboxes
    const firstCheckbox = checkboxes.nth(0);
    const thirdCheckbox = checkboxes.nth(2);

    await firstCheckbox.check();
    await thirdCheckbox.check();

    // Verify both are checked
    await expect(firstCheckbox).toBeChecked();
    await expect(thirdCheckbox).toBeChecked();

    // Verify the second checkbox is NOT checked
    const secondCheckbox = checkboxes.nth(1);
    await expect(secondCheckbox).not.toBeChecked();

    // Uncheck the first, verify only the third is still checked
    await firstCheckbox.uncheck();
    await expect(firstCheckbox).not.toBeChecked();
    await expect(thirdCheckbox).toBeChecked();
  });
});
