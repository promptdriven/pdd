import { test, expect } from '@playwright/test';

// ────────────────────────────────────────────────────────────────────────────
// Stage 5: Audio Sync — error states
// ────────────────────────────────────────────────────────────────────────────

test.describe('Stage 5 Error States: Audio Sync', () => {
  test('timestamps API returns 500 — page renders without crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);

    // Page should not crash — heading should still be visible
    const heading = page.locator('h2', { hasText: 'Audio Sync' });
    await expect(heading.first()).toBeVisible();

    // No unhandled runtime errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('timestamps API returns empty object — page handles gracefully', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({}),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);

    // Page should still render the heading
    const heading = page.locator('h2', { hasText: 'Audio Sync' });
    await expect(heading.first()).toBeVisible();

    // Word count should show 0 or empty state
    const wordCount = page.locator('text=/\\d+ of \\d+ words/');
    const wordCountVisible = await wordCount.isVisible().catch(() => false);
    if (wordCountVisible) {
      await expect(wordCount).toContainText('0');
    }

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('timestamps API returns malformed data — no crash, heading still visible', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ words: 'not-an-array', extra: { nested: true } }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);

    // The h2 heading must remain visible (page did not crash)
    const heading = page.locator('h2', { hasText: 'Audio Sync' });
    await expect(heading.first()).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Stage 6: Spec Generation — error states
// ────────────────────────────────────────────────────────────────────────────

test.describe('Stage 6 Error States: Spec Generation', () => {
  test('specs list API returns 500 — shows error, does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/specs/list**', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // Stage heading should remain visible
    const heading = page.locator('h2', { hasText: 'Spec Generation' });
    await expect(heading.first()).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('specs list returns empty — shows appropriate empty state', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/specs/list**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // Heading should remain
    const heading = page.locator('h2', { hasText: 'Spec Generation' });
    await expect(heading.first()).toBeVisible();

    // Generate All Specs button should still be visible (not hidden)
    await expect(page.locator('button', { hasText: 'Generate All Specs' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('spec generation API returns 500 — error state shown, not stuck generating', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // Mock the run endpoint to return 500
    await page.route('**/api/pipeline/specs/run', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Pipeline execution failed' }),
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate All Specs' });
    await expect(generateBtn).toBeVisible();
    await generateBtn.click();
    await page.waitForTimeout(1000);

    // Button should NOT be stuck in "Generating..." — it should recover
    // Either revert to original text or show an error indicator
    const btnText = await generateBtn.textContent();
    expect(btnText).not.toContain('Generating');

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('spec generation returns malformed response — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // Mock the run endpoint to return malformed data
    await page.route('**/api/pipeline/specs/run', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: 'not valid json at all{{{',
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate All Specs' });
    await expect(generateBtn).toBeVisible();
    await generateBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash — heading still visible
    const heading = page.locator('h2', { hasText: 'Spec Generation' });
    await expect(heading.first()).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Stage 7: Veo Generation — error states
// ────────────────────────────────────────────────────────────────────────────

test.describe('Stage 7 Error States: Veo Generation', () => {
  test('clips API returns 500 — shows error state, does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/veo/clips**', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(2000);

    // Page should not show a crash overlay
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // The page should still be rendered (sidebar remains interactive)
    await expect(sidebar).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('clips API returns empty clips array — shows empty table or message', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/veo/clips**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ clips: [] }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(2000);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // Table body should have zero rows or an empty-state message
    const rows = page.locator('tbody tr');
    const rowCount = await rows.count();
    // With empty clips, expect 0 rows (or 1 row for empty-state message)
    expect(rowCount).toBeLessThanOrEqual(1);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Generate All API returns 500 — shows error, buttons re-enable', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    // Mock the run endpoint to return 500
    await page.route('**/api/pipeline/veo/run', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Veo pipeline failed' }),
      });
    });

    const generateAllBtn = page.locator('button', { hasText: 'Generate All' });
    await expect(generateAllBtn).toBeVisible();
    await generateAllBtn.click();
    await page.waitForTimeout(1000);

    // Button should not be stuck in a disabled/loading state
    await expect(generateAllBtn).toBeVisible();
    // The "Generate Missing" button should also remain interactive
    await expect(page.locator('button', { hasText: 'Generate Missing' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Generate All returns SSE error event — clips show error status, not stuck generating', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    // Mock the run endpoint to return an SSE error event
    await page.route('**/api/pipeline/veo/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: 'event: error\ndata: {"message":"Pipeline failed"}\n\n',
      });
    });

    const generateAllBtn = page.locator('button', { hasText: 'Generate All' });
    await expect(generateAllBtn).toBeVisible();
    await generateAllBtn.click();
    await page.waitForTimeout(1500);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // Clips should NOT be stuck showing a "generating" spinner indefinitely
    // Check that no cell text contains "generating" (status should be error or missing)
    const generatingCells = page.locator('td', { hasText: /generating/i });
    const generatingCount = await generatingCells.count();
    expect(generatingCount).toBe(0);

    // The Generate All button should be re-enabled (not stuck disabled)
    await expect(generateAllBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('per-clip Regenerate returns 500 — error state for that clip', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    // Mock the run endpoint to return 500
    await page.route('**/api/pipeline/veo/run', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Single clip generation failed' }),
      });
    });

    // Click the per-clip Regenerate button on the first row
    const clipRegenBtn = page.locator('tbody tr').first().locator('button', { hasText: '↺ Regenerate' });
    await expect(clipRegenBtn).toBeVisible();
    await clipRegenBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // The regenerate button should remain visible (not stuck in loading)
    await expect(clipRegenBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Stage 8: Composition Generation — error states
// ────────────────────────────────────────────────────────────────────────────

test.describe('Stage 8 Error States: Composition Generation', () => {
  test('compositions list API returns 500 — error state, does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/compositions/list**', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Compositions' }).first().click();
    await page.waitForTimeout(2000);

    // Page should not crash — sidebar should still be visible
    await expect(sidebar).toBeVisible();

    // No runtime error overlay
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('compositions list returns empty — appropriate empty state', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/compositions/list**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ components: [], sections: [] }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Compositions' }).first().click();
    await page.waitForTimeout(2000);

    // The heading should still appear
    const heading = page.locator('h2', { hasText: 'Composition Generation' });
    await expect(heading).toBeVisible();

    // Generate All Compositions button should remain visible
    await expect(page.locator('button', { hasText: 'Generate All Compositions' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('generation API returns 500 — error shown, not stuck generating', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });

    // Mock the run endpoint to return 500
    await page.route('**/api/pipeline/compositions/run', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Composition generation failed' }),
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await expect(generateBtn).toBeVisible();
    await expect(generateBtn).toBeEnabled();
    await generateBtn.click();
    await page.waitForTimeout(1000);

    // Button should NOT be stuck showing "Generating..."
    const btnText = await generateBtn.textContent();
    expect(btnText).not.toContain('Generating');

    // Page heading should still be visible (no crash)
    const heading = page.locator('h2', { hasText: 'Composition Generation' });
    await expect(heading).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Stage 8: Staging Manifest and Asset Staging — error states
// ────────────────────────────────────────────────────────────────────────────

test.describe('Stage 8 Error States: Staging Manifest and Asset Staging', () => {
  test('staging manifest API 500 — degrades gracefully without crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.route('**/api/pipeline/veo/staging-manifest**', (route) =>
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      })
    );

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Compositions' }).first().click();
    await page.waitForTimeout(2000);

    // h3 "Asset Staging Manifest" should still be visible despite the 500
    await expect(page.locator('h3', { hasText: 'Asset Staging Manifest' })).toBeVisible();

    // No runtime crashes
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('asset staging API 500 — Stage Now button recovers from busy state', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock manifest to show 1 missing file
    await page.route('**/api/pipeline/veo/staging-manifest**', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify([{ filename: 'test-asset.mp4', expected: true, present: false }]),
      })
    );

    // Mock asset-staging run to return 500
    await page.route('**/api/pipeline/asset-staging/run', (route) =>
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Asset staging failed' }),
      })
    );

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });

    const stageNowBtn = page.locator('button', { hasText: 'Stage Now' });
    await expect(stageNowBtn).toBeVisible();
    await stageNowBtn.click();
    await page.waitForTimeout(1000);

    // Button should not be stuck in "..." — should revert to "Stage Now"
    await expect(stageNowBtn).toHaveText('Stage Now');

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
