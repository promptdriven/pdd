import { test, expect } from '@playwright/test';

test.describe('Stage 5: Audio Sync', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Audio Sync stage
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);
  });

  test('renders without crash (sectionGroups SegmentRange fix)', async ({ page }) => {
    // This test verifies the fix for: .join is not a function
    // The API returns sectionGroups as Record<string, SegmentRange> where
    // SegmentRange = { startSegment, endSegment }, but the component expected string[].
    // After the fix, the component normalizes SegmentRange objects to arrays.

    // No error overlay should appear
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('renders without crash (timestamps.filter fix)', async ({ page }) => {
    // This test verifies the fix for: timestamps.filter is not a function
    // The timestamps API returns { words: [...] } but the component expected a raw array.
    // After the fix, the component destructures the response.

    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays Save Config and Run Audio Sync buttons', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Save Config' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'Run Audio Sync' })).toBeVisible();
  });

  test('displays word count indicator', async ({ page }) => {
    // Should show "X of Y words" even if 0
    await expect(page.locator('text=/\\d+ of \\d+ words/')).toBeVisible();
  });

  test('displays Continue button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Continue' })).toBeVisible();
  });

  test('section grouping heading is visible with proper contrast', async ({ page }) => {
    // Bug: heading text was invisible (light text on white bg-white card).
    // The heading "Audio Sync Section Groups" must be visible to the user.
    const heading = page.locator('h2', { hasText: 'Audio Sync Section Groups' });
    await expect(heading).toBeVisible();

    // Verify the heading has dark text color (not inherited light theme color)
    const color = await heading.evaluate((el) => getComputedStyle(el).color);
    // Color should be dark (RGB values should not all be > 200)
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('section labels in grouping table are visible with proper contrast', async ({ page }) => {
    // Bug: section labels (e.g. "Cold Open") were invisible (inherited light text on white bg).
    // After fix, they should have explicit dark text color.
    await page.waitForTimeout(500);

    // Find the first section label cell in the table
    const firstSectionCell = page.locator('td').first();
    const cellText = await firstSectionCell.textContent();

    // Should have actual text content (not empty)
    expect(cellText).toBeTruthy();
    expect(cellText!.trim().length).toBeGreaterThan(0);

    // Verify the text color is dark (readable on white background)
    const color = await firstSectionCell.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('section grouping table headers are visible', async ({ page }) => {
    // Table headers "Section" and "Segment IDs (comma-separated)" should be readable
    const sectionHeader = page.locator('th', { hasText: 'Section' }).first();
    await expect(sectionHeader).toBeVisible();

    const segmentHeader = page.locator('th', { hasText: 'Segment IDs' });
    await expect(segmentHeader).toBeVisible();
  });

  test('word timestamp viewer heading is visible', async ({ page }) => {
    const heading = page.locator('h2', { hasText: 'Word Timestamp Viewer' });
    await expect(heading).toBeVisible();

    // Verify it has dark text color for readability on the white card
    const color = await heading.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('search input has placeholder text', async ({ page }) => {
    const searchInput = page.locator('input[placeholder="Search word\u2026"]');
    await expect(searchInput).toBeVisible();
  });

  test('section dropdown is present', async ({ page }) => {
    const select = page.locator('select');
    await expect(select).toBeVisible();
  });

  test('section grouping inputs accept text', async ({ page }) => {
    // Find the first segment input and type into it
    await page.waitForTimeout(500);
    const firstInput = page.locator('input[placeholder="segment1, segment2, segment3"]').first();
    await expect(firstInput).toBeVisible();
    await firstInput.fill('seg_001, seg_002');
    await expect(firstInput).toHaveValue('seg_001, seg_002');
  });

  test('word timestamp table headers are visible', async ({ page }) => {
    // The virtualized timestamp table should have headers: Word, Start, End, Segment ID
    await expect(page.locator('th', { hasText: 'Word' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Start' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'End' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Segment ID' }).first()).toBeVisible();
  });
});
