import { test, expect } from '@playwright/test';

test.describe('Cross-cutting features', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/', { waitUntil: 'domcontentloaded' });
    await expect(page.locator('button', { hasText: 'Pipeline' })).toBeVisible({
      timeout: 15000,
    });
  });

  test('page loads and displays Pipeline tab as active by default', async ({ page }) => {
    // Pipeline button should have the active border style
    const pipelineBtn = page.locator('button', { hasText: 'Pipeline' });
    await expect(pipelineBtn).toBeVisible();
    await expect(pipelineBtn).toHaveCSS('border-bottom-style', 'solid');

    // Review button should be visible but not active
    const reviewBtn = page.locator('button', { hasText: 'Review' });
    await expect(reviewBtn).toBeVisible();
  });

  test('all 10 sidebar stages are visible', async ({ page }) => {
    const sidebar = page.locator('aside');
    await expect(sidebar).toBeVisible();

    const stageLabels = [
      'Setup', 'Script', 'TTS Script', 'TTS Render',
      'Audio Sync', 'Spec Gen', 'Veo Gen', 'Compositions',
      'Render', 'Audit',
    ];

    for (const label of stageLabels) {
      const stageItem = sidebar.locator('button', { hasText: label }).first();
      await expect(stageItem).toBeVisible();
    }
  });

  test('sidebar stage numbers are shown 1 through 10', async ({ page }) => {
    const sidebar = page.locator('aside');
    for (let i = 1; i <= 10; i++) {
      await expect(sidebar.locator(`text=${i}`).first()).toBeVisible();
    }
  });

  test('default active stage is Setup (Stage 1)', async ({ page }) => {
    // Stage 1 heading should be visible
    const heading = page.locator('h2', { hasText: 'Stage 1: Project Setup' });
    await expect(heading).toBeVisible();
  });

  test('clicking a stage changes the panel content', async ({ page }) => {
    // Initially should show Stage 1
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    // Click on "Script" (Stage 2)
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Script' }).first().click();

    // Should now show Stage 2
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();
  });

  test('clicking all 10 stages loads without crash', async ({ page }) => {
    const sidebar = page.locator('aside');
    const stages = sidebar.locator('button');

    const count = await stages.count();
    expect(count).toBe(10);

    for (let i = 0; i < count; i++) {
      await stages.nth(i).click();
      // Verify no crash: main element should still be present or at minimum no error overlay
      // The Next.js error overlay contains "Runtime TypeError" text
      const errorOverlay = page.locator('text=Runtime TypeError');
      const hasError = await errorOverlay.isVisible().catch(() => false);
      expect(hasError).toBe(false);
    }
  });

  test('tab switching between Pipeline and Review works', async ({ page }) => {
    // Start on Pipeline
    const sidebar = page.locator('aside');
    await expect(sidebar).toBeVisible();

    // Click Review tab
    await page.locator('button', { hasText: 'Review' }).click();

    // Sidebar should disappear (Review tab has no sidebar)
    await expect(sidebar).not.toBeVisible();

    // Review content should show annotation tools or video player
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Switch back to Pipeline
    await page.locator('button', { hasText: 'Pipeline' }).click();

    // Sidebar should reappear
    await expect(sidebar).toBeVisible();
  });
});
