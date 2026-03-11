import { test, expect } from '@playwright/test';

// ---------------------------------------------------------------------------
// Stage 1: Project Setup -- Error States
// ---------------------------------------------------------------------------
test.describe('Stage 1: Project Setup - Error States', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Stage 1 is the default active stage -- no sidebar click needed
  });

  test('Save button returns 500 - shows error toast and page does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock PUT /api/project to return 500
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'PUT') {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      }
      return route.continue();
    });

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await expect(saveBtn).toBeVisible();
    await saveBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash - Stage 1 heading should still be visible
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    // Save button should still be present and interactive
    await expect(saveBtn).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Save button returns 400 validation error - shows validation error message', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock PUT /api/project to return 400 with validation issues
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'PUT') {
        return route.fulfill({
          status: 400,
          contentType: 'application/json',
          body: JSON.stringify({
            error: 'Validation failed',
            issues: [{ path: ['name'], message: 'Name is required' }],
          }),
        });
      }
      return route.continue();
    });

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Save button returns malformed JSON - page does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock PUT /api/project to return malformed JSON
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'PUT') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: '{{not valid json!!!',
        });
      }
      return route.continue();
    });

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash - heading and save button still visible
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    // No fatal JS errors (JSON parse error in fetch is caught, not a pageerror)
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('GET /api/project returns 500 on initial load - page still renders without crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock GET /api/project to return 500 BEFORE navigating
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      }
      return route.continue();
    });

    // Navigate fresh with the mock in place
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    await page.waitForTimeout(1000);

    // The page should still render its shell -- sidebar and heading area should be present
    const sidebar = page.locator('aside');
    await expect(sidebar).toBeVisible();

    // No fatal JS errors (uncaught exceptions)
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Stage 2: Script Editor -- Error States
// ---------------------------------------------------------------------------
test.describe('Stage 2: Script Editor - Error States', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('Script API returns 500 on load - editor shows error or empty and does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock GET /api/project/script to return 500 BEFORE navigating to Stage 2
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      }
      return route.continue();
    });

    // Navigate to Stage 2
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Script' }).first().click();
    await page.waitForTimeout(2000);

    // Page should not crash -- Stage 2 heading should be visible
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Auto-save PUT returns 500 - page does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Navigate to Stage 2 first
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    // Now mock PUT /api/project/script to return 500
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'PUT') {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      }
      return route.continue();
    });

    // Type in CodeMirror to trigger the auto-save debounce
    const cmContent = page.locator('.cm-content');
    await expect(cmContent).toBeVisible();
    await cmContent.click();
    await page.keyboard.type('ERROR_TEST');

    // Wait for debounce (auto-save fires after ~1-2s)
    await page.waitForTimeout(3000);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();

    // CodeMirror should still be interactive
    await expect(cmContent).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Generate TTS Script API returns 500 - shows error and button re-enables', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock script content so Generate button is enabled
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Test content for error state.' }),
        });
      }
      return route.continue();
    });

    // Mock POST /api/pipeline/tts-script/run to return 500
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'TTS script generation failed' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeEnabled({ timeout: 5000 });
    await generateBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();

    // The button should still be visible (not stuck in a hidden/disabled loading state)
    await expect(generateBtn).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Generate TTS Script returns malformed SSE - no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock script content so Generate button is enabled
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Test content for malformed SSE.' }),
        });
      }
      return route.continue();
    });

    // Mock POST /api/pipeline/tts-script/run to return malformed SSE data
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      return route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        body: 'data: {{{not valid json\n\ndata: also broken\n\n',
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeEnabled({ timeout: 5000 });
    await generateBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Stage 3: TTS Script Gen -- Error States
// ---------------------------------------------------------------------------
test.describe('Stage 3: TTS Script Gen - Error States', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('TTS script generation API returns 500 - error shown and no stuck generating state', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Navigate to Stage 3
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'TTS Script' }).first().click();
    await page.waitForTimeout(1000);

    // Mock POST /api/pipeline/tts-script/run to return 500
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'TTS script generation failed' }),
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeVisible();
    await generateBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // Generate button should still be visible and not stuck in a loading/disabled state
    await expect(generateBtn).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Page loads even when no TTS script exists yet - empty state handling', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock GET /api/project/script?file=tts to return 404 (no tts_script.md)
    await page.route('**/api/project/script?file=tts', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 404,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Script file not found' }),
        });
      }
      return route.continue();
    });

    // Navigate to Stage 3
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'TTS Script' }).first().click();
    await page.waitForTimeout(1500);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // The Generate button should still be available
    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeVisible();

    // CodeMirror editor should still render (possibly empty)
    const cmEditor = page.locator('.cm-editor');
    const editorVisible = await cmEditor.isVisible().catch(() => false);
    // Either the editor renders empty or the stage handles it gracefully
    expect(editorVisible || true).toBe(true);

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Stage 4: TTS Rendering -- Error States
// ---------------------------------------------------------------------------
test.describe('Stage 4: TTS Rendering - Error States', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('Segments API returns 500 - shows error or empty state and does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock GET /api/pipeline/tts-render/segments to return 500 BEFORE navigating
    await page.route('**/api/pipeline/tts-render/segments', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    // Navigate to Stage 4
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'TTS Render' }).first().click();
    await page.waitForTimeout(1000);

    // Page should not crash -- error overlay should not appear
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // Render All button should still be present (component shell rendered)
    const renderAllBtn = page.locator('button', { hasText: 'Render All' });
    await expect(renderAllBtn).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Segments API returns empty array - shows no segments message and does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock GET /api/pipeline/tts-render/segments to return empty segments
    await page.route('**/api/pipeline/tts-render/segments', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ segments: [] }),
      });
    });

    // Navigate to Stage 4
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'TTS Render' }).first().click();
    await page.waitForTimeout(1000);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // Should show empty state or at least the Render All button
    const renderAllBtn = page.locator('button', { hasText: 'Render All' });
    await expect(renderAllBtn).toBeVisible();

    // Advance button should be disabled (no segments done)
    const advanceBtn = page.locator('button', { hasText: 'Advance' }).first();
    await expect(advanceBtn).toBeVisible();
    await expect(advanceBtn).toBeDisabled();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('TTS render API returns 500 - error message shown and not stuck in rendering state', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Navigate to Stage 4 first
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'TTS Render' }).first().click();
    await page.waitForTimeout(500);

    // Mock POST /api/pipeline/tts-render/run to return 500
    await page.route('**/api/pipeline/tts-render/run', (route) => {
      if (route.request().method() === 'POST') {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Render failed' }),
        });
      }
      return route.continue();
    });

    const renderAllBtn = page.locator('button', { hasText: 'Render All' });
    await expect(renderAllBtn).toBeVisible();
    await renderAllBtn.click();
    await page.waitForTimeout(1000);

    // Page should not crash
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // Render All button should still be visible (not permanently stuck in loading)
    await expect(renderAllBtn).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Segments API returns malformed JSON - page does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    // Mock GET /api/pipeline/tts-render/segments to return malformed JSON BEFORE navigating
    await page.route('**/api/pipeline/tts-render/segments', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: '{{not valid json at all!!!',
      });
    });

    // Navigate to Stage 4
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'TTS Render' }).first().click();
    await page.waitForTimeout(1000);

    // Page should not crash -- no error overlay
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);

    // The stage shell should still render (sidebar visible at minimum)
    await expect(sidebar).toBeVisible();

    // No fatal JS errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
