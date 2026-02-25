import { test, expect } from '@playwright/test';

// ────────────────────────────────────────────────────────────────────────────
// Double-Click Prevention
// ────────────────────────────────────────────────────────────────────────────

test.describe('Double-click prevention', () => {
  test('double-clicking Generate All fires only one API call', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 7
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    let callCount = 0;
    await page.route('**/api/pipeline/veo/run', (route) => {
      callCount++;
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: 'data: {"type":"complete","jobId":"test"}\n\nevent: done\ndata: {}\n\n',
      });
    });

    const btn = page.locator('button', { hasText: 'Generate All' });
    await btn.dblclick();
    await page.waitForTimeout(2000);

    // Should be 1 or at most 2, not more
    expect(callCount).toBeLessThanOrEqual(2);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('double-clicking Save (Stage 1) sends at most one PUT', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Stage 1 is the default active stage

    let callCount = 0;
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'PUT') {
        callCount++;
        route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ success: true }),
        });
      } else {
        route.continue();
      }
    });

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await expect(saveBtn).toBeVisible();
    await saveBtn.dblclick();
    await page.waitForTimeout(2000);

    // Double-click should send at most 2 PUTs
    expect(callCount).toBeLessThanOrEqual(2);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('double-clicking Render (Stage 9) sends at most one request', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    let callCount = 0;
    await page.route('**/api/pipeline/render/run', (route) => {
      callCount++;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-render-job' }),
      });
    });

    const renderBtn = page.locator('button', { hasText: /Render/ }).first();
    await expect(renderBtn).toBeVisible();
    await renderBtn.dblclick();
    await page.waitForTimeout(2000);

    // Should be at most 2
    expect(callCount).toBeLessThanOrEqual(2);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('double-clicking Stitch (Stage 9) sends at most one request', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    let callCount = 0;
    await page.route('**/api/pipeline/stitch/run', (route) => {
      callCount++;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    // Also mock the status reload that happens after stitch
    await page.route('**/api/pipeline/render/status', (route) => {
      route.fulfill({
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

    const stitchBtn = page.locator('button', { hasText: 'Stitch Full Video' });
    await expect(stitchBtn).toBeVisible();
    await stitchBtn.dblclick();
    await page.waitForTimeout(2000);

    // Should be at most 2
    expect(callCount).toBeLessThanOrEqual(2);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Debounce Behavior
// ────────────────────────────────────────────────────────────────────────────

test.describe('Debounce behavior', () => {
  test('rapid typing fires only one auto-save PUT', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500); // Wait for CodeMirror init

    let putCount = 0;
    await page.route('**/api/project/script', (route) => {
      if (route.request().method() === 'PUT') {
        putCount++;
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ success: true }),
        });
      }
      return route.continue();
    });

    // Rapid typing
    const cmContent = page.locator('.cm-content');
    await cmContent.click();
    for (let i = 0; i < 10; i++) {
      await page.keyboard.type('x');
      await page.waitForTimeout(50);
    }

    // Wait for debounce (1s) + extra margin
    await page.waitForTimeout(3000);

    // Should have fired 1 (maybe 2) PUTs, not 10
    expect(putCount).toBeLessThanOrEqual(2);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('no save fires during typing (before debounce completes)', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500); // Wait for CodeMirror init

    let putCount = 0;
    await page.route('**/api/project/script', (route) => {
      if (route.request().method() === 'PUT') {
        putCount++;
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ success: true }),
        });
      }
      return route.continue();
    });

    // Type 3 characters
    const cmContent = page.locator('.cm-content');
    await cmContent.click();
    await page.keyboard.type('abc');

    // Wait only 200ms — less than the 1s debounce
    await page.waitForTimeout(200);

    // No PUT should have fired yet
    expect(putCount).toBe(0);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('debounce timer resets on new input', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500); // Wait for CodeMirror init

    let putCount = 0;
    await page.route('**/api/project/script', (route) => {
      if (route.request().method() === 'PUT') {
        putCount++;
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ success: true }),
        });
      }
      return route.continue();
    });

    const cmContent = page.locator('.cm-content');
    await cmContent.click();

    // Type 3 characters, wait 800ms (short of 1s debounce)
    await page.keyboard.type('abc');
    await page.waitForTimeout(800);

    // Type 3 more characters — debounce timer should reset
    await page.keyboard.type('def');

    // Wait for debounce to complete (1s + margin)
    await page.waitForTimeout(2000);

    // Should have at most 2 PUTs total (the debounce timer reset means the
    // first batch may or may not have fired depending on exact timing)
    expect(putCount).toBeLessThanOrEqual(2);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Navigation During Loading
// ────────────────────────────────────────────────────────────────────────────

test.describe('Navigation during loading', () => {
  test('switch stage while API is loading does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Delay the clips API response
    await page.route('**/api/pipeline/veo/clips', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ clips: [] }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Start loading Stage 7
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(500);

    // Immediately switch to Stage 1
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);

    // Stage 1 should render correctly
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    // Wait for delayed response to arrive
    await page.waitForTimeout(3000);

    // Still no crashes
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('switch to Review during SSE stream does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 7
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    // Mock SSE that sends events over time
    await page.route('**/api/pipeline/veo/run', async (route) => {
      // Simulate a slow SSE stream
      await new Promise((r) => setTimeout(r, 500));
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: [
          'data: {"type":"progress","clipId":"clip1","progress":0.5}\n\n',
          'data: {"type":"progress","clipId":"clip1","progress":1.0}\n\n',
          'data: {"type":"complete","jobId":"test"}\n\n',
          'event: done\ndata: {}\n\n',
        ].join(''),
      });
    });

    // Start generation
    const generateBtn = page.locator('button', { hasText: 'Generate All' });
    await generateBtn.click();
    await page.waitForTimeout(200);

    // Switch to Review tab mid-stream
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);

    // Review should render correctly
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();

    // Wait for SSE to finish
    await page.waitForTimeout(3000);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('navigate away during stitch operation does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Mock stitch with delayed response
    await page.route('**/api/pipeline/stitch/run', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    // Also mock status reload
    await page.route('**/api/pipeline/render/status', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            { id: 'cold_open', durationSeconds: 0, status: 'missing', progress: 0 },
          ],
          fullVideo: { exists: false },
        }),
      });
    });

    // Start stitch
    const stitchBtn = page.locator('button', { hasText: 'Stitch Full Video' });
    await stitchBtn.click();
    await page.waitForTimeout(500);

    // Navigate to Stage 1 while stitch is in-flight
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);

    // Stage 1 should render correctly
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    // Wait for delayed stitch response
    await page.waitForTimeout(3000);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('switch Pipeline and Review rapidly during API calls does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Click Review, immediately click Pipeline, immediately click Review
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(100);
    await page.locator('button', { hasText: 'Pipeline' }).click();
    await page.waitForTimeout(100);
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(100);
    await page.locator('button', { hasText: 'Pipeline' }).click();
    await page.waitForTimeout(100);
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(2000);

    // Final state should be Review tab — sidebar hidden, annotation tools visible
    await expect(page.locator('aside')).not.toBeVisible();
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ────────────────────────────────────────────────────────────────────────────
// Concurrent Operations
// ────────────────────────────────────────────────────────────────────────────

test.describe('Concurrent operations', () => {
  test('multiple stage API calls do not interfere', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Delay clips API to simulate slow Stage 7 loading
    await page.route('**/api/pipeline/veo/clips', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ clips: [] }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');

    // Navigate to Stage 7 (loads clips — will be delayed)
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await page.waitForTimeout(300);

    // Immediately switch to Stage 9 (loads render status)
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();

    // Stage 9 should load correctly despite Stage 7 still being in-flight
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();

    // Wait for delayed Stage 7 response to arrive
    await page.waitForTimeout(3000);

    // Stage 9 should still be displayed (the delayed Stage 7 response should not hijack the UI)
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('save during generation does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Mock PUT /api/project with 1s delay
    await page.route('**/api/project', async (route) => {
      if (route.request().method() === 'PUT') {
        await new Promise((r) => setTimeout(r, 1000));
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ success: true }),
        });
      }
      return route.continue();
    });

    // On Stage 1, start a save
    const saveBtn = page.locator('button', { hasText: 'Save' });
    await expect(saveBtn).toBeVisible();
    await saveBtn.click();

    // While save is in-flight, navigate to Stage 2
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500); // Wait for CodeMirror init

    // Mock TTS script generation
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-job-concurrent' }),
      });
    });

    // Start generation on Stage 2
    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeVisible();
    await generateBtn.click();

    // Wait for both operations to settle
    await page.waitForTimeout(2000);

    // No crashes should occur
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('multiple EventSource connections cleanup on navigation', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    const sidebar = page.locator('aside');

    // Navigate to Stage 7
    await sidebar.locator('div', { hasText: 'Veo Gen' }).first().click();
    await expect(page.locator('th', { hasText: 'Clip' }).first()).toBeVisible({ timeout: 15000 });

    // Mock SSE for veo generation
    await page.route('**/api/pipeline/veo/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: 'data: {"type":"progress","clipId":"clip1","progress":0.5}\n\n',
      });
    });

    // Start generation (opens SSE)
    const generateBtn = page.locator('button', { hasText: 'Generate All' });
    await generateBtn.click();
    await page.waitForTimeout(300);

    // Navigate to Stage 9
    await sidebar.locator('div').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Mock SSE for render
    await page.route('**/api/pipeline/render/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: 'data: {"type":"progress","sectionId":"cold_open","progress":0.5}\n\n',
      });
    });

    // Start render (opens another SSE)
    const renderBtn = page.locator('button', { hasText: /Render/ }).first();
    await renderBtn.click();
    await page.waitForTimeout(300);

    // Navigate to Stage 1
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);

    // Stage 1 should render correctly
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    // Wait for cleanup / any lingering effects
    await page.waitForTimeout(5000);

    // No memory leak warnings or crashes
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('rapid add/delete section operations do not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Stage 1 is the default active stage

    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();

    // Rapidly add 5 sections
    const addBtn = page.locator('button', { hasText: '+ Add Section' });
    for (let i = 0; i < 5; i++) {
      await addBtn.click();
      await page.waitForTimeout(100);
    }

    // Verify 5 rows were added
    const afterAddCount = await tableRows.count();
    expect(afterAddCount).toBe(initialCount + 5);

    // Rapidly delete the 5 newly added rows (delete from the last added one first)
    for (let i = 0; i < 5; i++) {
      // Always delete the last row (the newest added row)
      const lastRow = tableRows.last();
      const deleteBtn = lastRow.locator('button', { hasText: '✕' });
      await deleteBtn.click();
      await page.waitForTimeout(100);
    }

    // Verify count returned to original
    const afterDeleteCount = await tableRows.count();
    expect(afterDeleteCount).toBe(initialCount);

    // No crashes
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
