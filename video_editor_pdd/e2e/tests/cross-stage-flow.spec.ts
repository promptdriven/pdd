import { test, expect } from '@playwright/test';

// ────────────────────────────────────────────────────────────────────────────
// Navigation Flow Tests
// ────────────────────────────────────────────────────────────────────────────

test.describe('Cross-stage navigation flow', () => {
  test('navigate forward through all 10 stages', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Stage 1 is default
    await expect(page.locator('h2', { hasText: 'Stage 1' })).toBeVisible();

    // Navigate to each subsequent stage via sidebar
    const stages = [
      { nav: 'Script', heading: 'Stage 2' },
      { nav: 'TTS Script', heading: 'Stage 3' },
      { nav: 'TTS Render', heading: 'Stage 4' },
      { nav: 'Audio Sync', heading: 'Stage 5' },
      { nav: 'Spec Gen', heading: 'Stage 6' },
      { nav: 'Veo Gen', heading: 'Stage 7' },
      { nav: 'Compositions', heading: 'Stage 8' },
    ];

    for (const stage of stages) {
      const sidebar = page.locator('aside');
      await sidebar.locator('div', { hasText: stage.nav }).first().click();
      await page.waitForTimeout(1000);
      await expect(page.locator('h2', { hasText: stage.heading })).toBeVisible({ timeout: 15000 });
    }

    // Stage 9
    await page.locator('aside').locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible({ timeout: 15000 });

    // Stage 10
    await page.locator('aside').locator('div').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });
  });

  test('Pipeline and Review tab switching preserves active stage', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 5 (Audio Sync)
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 5' }).first()).toBeVisible({ timeout: 15000 });

    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);
    await expect(page.locator('aside')).not.toBeVisible();
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Switch back to Pipeline
    await page.locator('button', { hasText: 'Pipeline' }).click();
    await page.waitForTimeout(500);

    // Stage 5 should still be active
    await expect(page.locator('aside')).toBeVisible();
    await expect(page.locator('h2', { hasText: 'Stage 5' }).first()).toBeVisible({ timeout: 15000 });
  });

  test('rapid stage switching does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');

    // Click through stages rapidly: 1 -> 7 -> 3 -> 9 -> 2 -> 10
    // Stage 1 is already active

    // Stage 7
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(100);

    // Stage 3
    await sidebar.locator('div', { hasText: 'TTS Script' }).first().click();
    await page.waitForTimeout(100);

    // Stage 9
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await page.waitForTimeout(100);

    // Stage 2
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    await page.waitForTimeout(100);

    // Stage 10
    await sidebar.locator('div').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(2000);

    // Last stage (10) heading should be visible
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });

    // No application errors should have occurred
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Continue button advances to next stage', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 7 (Veo Gen)
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    // Click Continue button
    const continueBtn = page.locator('button', { hasText: 'Continue' });
    await expect(continueBtn).toBeVisible();
    await continueBtn.click();
    await page.waitForTimeout(1000);

    // Should advance to Stage 8 (Composition Generation)
    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible({ timeout: 15000 });
  });

  test('back navigation to previously visited stage', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 7
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 7' })).toBeVisible({ timeout: 15000 });

    // Navigate back to Stage 1
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(1000);

    // Stage 1 heading and project name input should be visible
    await expect(page.locator('h2', { hasText: 'Stage 1' })).toBeVisible({ timeout: 15000 });
    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();
    await expect(nameInput).not.toHaveValue('');
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Data Consistency Tests
// ────────────────────────────────────────────────────────────────────────────

test.describe('Cross-stage data consistency', () => {
  test('project config visible across stages', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Stage 1: verify project name input has content
    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();
    const projectName = await nameInput.inputValue();
    expect(projectName.length).toBeGreaterThan(0);

    // Stage 7: verify sections are present in clip table
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });
    const stage7Rows = page.locator('tbody tr');
    const stage7Count = await stage7Rows.count();
    expect(stage7Count).toBeGreaterThan(0);

    // Stage 9: verify sections are present in render table
    await page.locator('aside').locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });
    const stage9Rows = page.locator('tbody tr');
    const stage9Count = await stage9Rows.count();
    expect(stage9Count).toBeGreaterThan(0);

    // Both stages should have the same number of section rows
    expect(stage7Count).toBe(stage9Count);
  });

  test('section count is consistent across stages', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Stage 1: count section rows
    const stage1Rows = page.locator('tbody tr');
    const stage1Count = await stage1Rows.count();
    expect(stage1Count).toBeGreaterThan(0);

    // Stage 7: count clip rows
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });
    const stage7Rows = page.locator('tbody tr');
    const stage7Count = await stage7Rows.count();

    // Stage 9: count render rows
    await page.locator('aside').locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });
    const stage9Rows = page.locator('tbody tr');
    const stage9Count = await stage9Rows.count();

    // All should match
    expect(stage7Count).toBe(stage1Count);
    expect(stage9Count).toBe(stage1Count);
  });

  test('stage sidebar shows stage numbers and labels', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await expect(sidebar).toBeVisible();

    const stageLabels = [
      'Setup', 'Script', 'TTS Script', 'TTS Render',
      'Audio Sync', 'Spec Gen', 'Veo Gen', 'Compositions',
      'Render', 'Audit',
    ];

    for (const label of stageLabels) {
      const stageItem = sidebar.locator('div', { hasText: label }).first();
      await expect(stageItem).toBeVisible();
    }

    // Verify all 10 stage numbers are present
    for (let i = 1; i <= 10; i++) {
      await expect(sidebar.locator(`text=${i}`).first()).toBeVisible();
    }
  });

  test('active stage highlight in sidebar changes on navigation', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    const sidebarItems = sidebar.locator('> div');

    // Navigate to Stage 5 (Audio Sync) -- index 4 (0-based)
    await sidebar.locator('div', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 5' }).first()).toBeVisible({ timeout: 15000 });

    // Get the computed background color of the Stage 5 sidebar item
    const stage5Item = sidebarItems.nth(4);
    const stage5Bg = await stage5Item.evaluate((el) => getComputedStyle(el).backgroundColor);

    // Navigate to Stage 7 (Veo Gen) -- index 6 (0-based)
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 7' })).toBeVisible({ timeout: 15000 });

    // Stage 7 sidebar item should now have the active background
    const stage7Item = sidebarItems.nth(6);
    const stage7Bg = await stage7Item.evaluate((el) => getComputedStyle(el).backgroundColor);

    // Stage 5 should no longer have the active background
    const stage5BgAfter = await stage5Item.evaluate((el) => getComputedStyle(el).backgroundColor);

    // The newly active stage (7) should have a different bg than the now-inactive stage (5)
    expect(stage7Bg).not.toBe(stage5BgAfter);
  });

  test('sidebar stage numbers are sequential 1 through 10', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    const sidebarItems = sidebar.locator('> div');

    // Verify there are exactly 10 sidebar items
    const count = await sidebarItems.count();
    expect(count).toBe(10);

    // Verify each item contains its sequential number
    for (let i = 0; i < 10; i++) {
      const itemText = await sidebarItems.nth(i).textContent();
      expect(itemText).toContain(`${i + 1}`);
    }
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Error Recovery Tests
// ────────────────────────────────────────────────────────────────────────────

test.describe('Cross-stage error recovery', () => {
  test('navigate away from loading stage does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');

    // Navigate to Stage 7 (which loads clips from API)
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();

    // Immediately switch to Stage 1 before loading completes
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(2000);

    // Stage 1 should render correctly
    await expect(page.locator('h2', { hasText: 'Stage 1' })).toBeVisible({ timeout: 15000 });
    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();

    // No application errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('stage loads normally after previous stage had API error', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock Stage 7 clips to fail
    await page.route('**/api/pipeline/veo/clips', (route) => {
      route.fulfill({ status: 500, body: JSON.stringify({ error: 'fail' }) });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Visit Stage 7 (will fail)
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(2000);

    // Remove the mock and navigate to Stage 9
    await page.unroute('**/api/pipeline/veo/clips');
    await page.locator('aside').locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await page.waitForTimeout(2000);

    // Stage 9 should load fine
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible({ timeout: 15000 });

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('return to Review tab after viewing Pipeline stages', async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Start by going to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Switch to Pipeline and navigate to Stage 5
    await page.locator('button', { hasText: 'Pipeline' }).click();
    await page.waitForTimeout(500);
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 5' }).first()).toBeVisible({ timeout: 15000 });

    // Switch back to Review
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);

    // Video player and annotation tools should be visible
    await expect(page.locator('text=Play/Pause')).toBeVisible();
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();
  });

  test('multiple tab switches between Pipeline and Review do not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Switch back and forth 5 times: Pipeline -> Review -> Pipeline -> Review -> Pipeline -> Review -> Pipeline -> Review -> Pipeline -> Review
    for (let i = 0; i < 5; i++) {
      await page.locator('button', { hasText: 'Review' }).click();
      await page.waitForTimeout(200);
      await page.locator('button', { hasText: 'Pipeline' }).click();
      await page.waitForTimeout(200);
    }

    // End on Pipeline — verify sidebar is visible and no crash
    await expect(page.locator('aside')).toBeVisible();

    // Switch to Review one final time — verify Review content is intact
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('navigate to every stage and verify no pageerror events', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');

    // Stage 1 is already active
    await expect(page.locator('h2', { hasText: 'Stage 1' })).toBeVisible();
    await page.waitForTimeout(500);

    // Stage 2
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 15000 });

    // Stage 3
    await sidebar.locator('div', { hasText: 'TTS Script' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 3' })).toBeVisible({ timeout: 15000 });

    // Stage 4
    await sidebar.locator('div', { hasText: 'TTS Render' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 4' })).toBeVisible({ timeout: 15000 });

    // Stage 5
    await sidebar.locator('div', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 5' }).first()).toBeVisible({ timeout: 15000 });

    // Stage 6
    await sidebar.locator('div', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 6' })).toBeVisible({ timeout: 15000 });

    // Stage 7
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 7' })).toBeVisible({ timeout: 15000 });

    // Stage 8
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible({ timeout: 15000 });

    // Stage 9
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible({ timeout: 15000 });

    // Stage 10
    await sidebar.locator('div').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(1000);
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });

    // Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(1000);
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Verify zero application errors across all navigations
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
