import { test, expect } from '@playwright/test';

test.describe('Stage 6: Spec Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Spec Gen stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);
  });

  test('renders without crash', async ({ page }) => {
    // No runtime error overlay should appear
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays stage heading', async ({ page }) => {
    const heading = page.locator('h2', { hasText: 'Stage 6' });
    await expect(heading).toBeVisible();
    await expect(heading).toContainText('Spec Generation');
  });

  test('displays Generate All Specs button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate All Specs' })).toBeVisible();
  });

  test('displays Continue button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Continue' })).toBeVisible();
  });

  test('renders section accordion cards from project.json', async ({ page }) => {
    // The project has 7 sections; each should appear as a card with its label
    await expect(page.locator('text=Cold Open').first()).toBeVisible();
    await expect(page.locator('text=Part 1: Economics').first()).toBeVisible();
    await expect(page.locator('text=Closing').first()).toBeVisible();
  });

  test('section labels have readable dark text on white card (dark theme fix)', async ({ page }) => {
    // Bug fix: section toggle button text was white-on-white in dark theme.
    // After fix, it should have explicit dark text color (text-slate-800).
    const sectionBtn = page.locator('button', { hasText: 'Cold Open' }).first();
    await expect(sectionBtn).toBeVisible();

    const color = await sectionBtn.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Dark text: RGB values should NOT all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('each section has a Regenerate button', async ({ page }) => {
    // Wait for section data to load (Loading spec list... disappears)
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });
    // The Regenerate button text includes a unicode arrow: "↺ Regenerate"
    const regenerateButtons = page.locator('button:has-text("Regenerate")');
    const count = await regenerateButtons.count();
    expect(count).toBeGreaterThanOrEqual(7);
  });

  test('file table displays Type, Path, Status, Actions headers', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Type' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Path' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Status' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Actions' }).first()).toBeVisible();
  });

  test('file status shows missing when spec files do not exist', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });
    // All spec files are "missing" since specs/ directory is empty
    const missingBadges = page.locator('text=missing');
    await expect(missingBadges.first()).toBeVisible();
    const count = await missingBadges.count();
    expect(count).toBeGreaterThanOrEqual(1);
  });

  test('spec file paths are visible in the table', async ({ page }) => {
    // Paths like "specs/00-cold-open/spec.md" should be visible
    await expect(page.locator('text=specs/').first()).toBeVisible();
  });

  test('accordion sections can collapse and expand', async ({ page }) => {
    // Click on the Cold Open toggle button to collapse
    const toggleBtn = page.locator('button', { hasText: 'Cold Open' }).first();
    await toggleBtn.click();
    await page.waitForTimeout(300);

    // The file table for Cold Open should be hidden
    // Check that "specs/00-cold-open" text is no longer visible
    const coldOpenPath = page.locator('text=specs/00-cold-open/spec.md');
    const isVisible = await coldOpenPath.isVisible().catch(() => false);
    expect(isVisible).toBe(false);

    // Click again to expand
    await toggleBtn.click();
    await page.waitForTimeout(300);
    await expect(coldOpenPath).toBeVisible();
  });

  test('Spec Generation Logs details element is present', async ({ page }) => {
    await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
    await page.waitForTimeout(300);
    const logsSummary = page.locator('summary', { hasText: 'Spec Generation Logs' });
    await expect(logsSummary).toBeVisible();
  });

  test('no console errors on load', async ({ page }) => {
    // This test uses the beforeEach navigation (already on Stage 6).
    // We just verify no page errors were captured.
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Re-click on Stage 6 to trigger a fresh load within the already-loaded page
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);
    await sidebar.locator('div', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(2000);

    // Filter out non-application errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
