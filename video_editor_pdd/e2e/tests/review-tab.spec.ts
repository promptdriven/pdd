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
});
