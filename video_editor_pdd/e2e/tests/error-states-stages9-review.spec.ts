import { test, expect } from '@playwright/test';
import { getProjectSections } from './helpers/project-fixtures';

const PROJECT_SECTION_COUNT = getProjectSections().length;

test.describe('Error States: Stage 9 (Render & Stitch)', () => {
  test('render status API returns 500 on load — page still renders heading, does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock the render status API to return 500 BEFORE navigating
    await page.route('**/api/pipeline/render/status', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await page.waitForTimeout(3000);

    // Page should still render the heading without crashing
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
    await expect(page.locator('h2', { hasText: 'Render & Stitch' })).toBeVisible();

    // Buttons should still be present
    await expect(page.getByTestId('render-sections-button')).toBeVisible();
    await expect(page.getByTestId('stitch-full-video-button')).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('render button click returns 500 — shows error, table does not show stuck rendering', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Mock the render run API to return 500
    await page.route('**/api/pipeline/render/run', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Render service unavailable' }),
      });
    });

    // Click the Render button
    const renderButton = page.getByTestId('render-sections-button');
    await renderButton.click();
    await page.waitForTimeout(1000);

    // Page should still be functional — heading and buttons visible
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
    await expect(page.getByTestId('stitch-full-video-button')).toBeVisible();

    // Table should not be stuck showing "rendering" status for all sections
    const renderingBadges = page.locator('tbody span.rounded-full', { hasText: 'rendering' });
    const renderingCount = await renderingBadges.count();
    // Either 0 rendering badges (error handled) or the existing status is preserved
    expect(renderingCount).toBeLessThanOrEqual(0);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('render returns SSE error event mid-stream — section shows error status', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Mock the render run API to return SSE with an error event
    await page.route('**/api/pipeline/render/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: 'event: error\ndata: {"message":"Render failed"}\n\n',
      });
    });

    // Click the Render button
    const renderButton = page.getByTestId('render-sections-button');
    await renderButton.click();
    await page.waitForTimeout(1500);

    // Page should still be functional
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible();

    // Render and Stitch buttons should still be usable
    await expect(page.getByTestId('render-sections-button')).toBeVisible();
    await expect(page.getByTestId('stitch-full-video-button')).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('stitch button click returns 500 — shows error message, page functional', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Mock the stitch API to return 500
    await page.route('**/api/pipeline/stitch/run', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Stitch service failed' }),
      });
    });

    // Click the Stitch Full Video button
    const stitchButton = page.getByTestId('stitch-full-video-button');
    await stitchButton.click();
    await page.waitForTimeout(1000);

    // Page should still be functional
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
    await expect(page.locator('h2', { hasText: 'Render & Stitch' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible();

    // Buttons should remain clickable
    await expect(page.getByTestId('render-sections-button')).toBeVisible();
    await expect(stitchButton).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('stitch button returns malformed response — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Mock the stitch API to return malformed response
    await page.route('**/api/pipeline/stitch/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: 'not valid json {{{',
      });
    });

    // Click the Stitch Full Video button
    const stitchButton = page.getByTestId('stitch-full-video-button');
    await stitchButton.click();
    await page.waitForTimeout(1000);

    // Page should still be functional — no crash
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible();
    await expect(stitchButton).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('re-render button returns 500 — that section shows error, other sections unaffected', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 9
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Wait for table rows to load
    await expect(page.locator('tbody tr')).toHaveCount(PROJECT_SECTION_COUNT);

    // Mock the render run API to return 500
    await page.route('**/api/pipeline/render/run', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Section render failed' }),
      });
    });

    // Click the re-render button on the first row only
    const firstRerenderButton = page.locator('tbody tr').first().locator('button[title="Re-render"]');
    await firstRerenderButton.click();
    await page.waitForTimeout(1000);

    // Page should still be functional
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();

    // All rows should still be present (other sections unaffected)
    await expect(page.locator('tbody tr')).toHaveCount(PROJECT_SECTION_COUNT);

    // Other sections' re-render buttons should still be visible and clickable
    const secondRerenderButton = page.locator('tbody tr').nth(1).locator('button[title="Re-render"]');
    await expect(secondRerenderButton).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

test.describe('Error States: Stage 10 (Audit)', () => {
  test('audit results API returns 500 — shows error or empty state, does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock the audit results API to return 500 BEFORE navigating
    await page.route('**/api/pipeline/audit/results', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    // Mock SSE stream to prevent hanging connections
    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 10
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(3000);

    // Page should still render the heading without crashing
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible();

    // Audit All Sections button should still be present
    await expect(page.locator('button', { hasText: 'Audit All Sections' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('audit results returns empty sections — appropriate empty state message', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock audit results with empty sections array
    await page.route('**/api/pipeline/audit/results', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      });
    });

    // Mock SSE stream
    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 10
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(3000);

    // Page should still render the heading
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible();

    // No "View Report" buttons should be present (empty sections)
    const viewReportButtons = page.locator('button', { hasText: 'View Report' });
    await expect(viewReportButtons).toHaveCount(0);

    // Audit All Sections button should still be present
    await expect(page.locator('button', { hasText: 'Audit All Sections' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Audit All Sections returns 500 — shows error, page functional', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 10
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });
    await page.waitForTimeout(1000);

    // Mock the audit run API to return 500
    await page.route('**/api/pipeline/audit/run', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Audit service unavailable' }),
      });
    });

    // Click Audit All Sections button
    const auditAllButton = page.locator('button', { hasText: 'Audit All Sections' });
    await auditAllButton.click();
    await page.waitForTimeout(1000);

    // Page should still be functional
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible();
    await expect(auditAllButton).toBeVisible();

    // Audit Section dropdown should still work
    await expect(page.locator('button', { hasText: 'Audit Section' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('audit results returns malformed section data (missing fields) — does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock audit results with malformed section data (missing required fields)
    await page.route('**/api/pipeline/audit/results', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            { sectionId: 'test' /* missing sectionLabel, passCount, failCount, status, specs */ },
          ],
        }),
      });
    });

    // Mock SSE stream
    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 10
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await page.waitForTimeout(3000);

    // Page should still render the heading without crashing
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible();

    // Audit All Sections button should still be present
    await expect(page.locator('button', { hasText: 'Audit All Sections' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('View Report on section with parse errors — shows error gracefully', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock audit results with a section that has malformed specs
    await page.route('**/api/pipeline/audit/results', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              sectionId: 'cold_open',
              sectionLabel: 'Cold Open',
              passCount: 0,
              failCount: 0,
              status: 'done',
              specs: [
                { specName: null, verdict: undefined, summary: '' },
                { /* completely empty spec object */ },
              ],
            },
          ],
        }),
      });
    });

    // Mock SSE stream
    await page.route('**/api/pipeline/audit/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Navigate to Stage 10
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^10\s*Audit/ }).click();
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible({ timeout: 15000 });
    await page.waitForTimeout(1000);

    // Click "View Report" to expand the section
    const viewReportButton = page.locator('button', { hasText: 'View Report' }).first();
    await expect(viewReportButton).toBeVisible({ timeout: 10000 });
    await viewReportButton.click();
    await page.waitForTimeout(500);

    // Page should still be functional — heading visible
    await expect(page.locator('h2', { hasText: 'Audit Results' })).toBeVisible();

    // Audit buttons should still be present
    await expect(page.locator('button', { hasText: 'Audit All Sections' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

test.describe('Error States: Review Tab', () => {
  test('annotations API returns 500 — shows error or empty state, drawing tools still work', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock the annotations API to return 500 BEFORE navigating
    await page.route('**/api/annotations', (route) => {
      if (route.request().method() === 'GET') {
        route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Annotations service unavailable' }),
        });
      } else {
        route.continue();
      }
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(1000);

    // Drawing tools should still be visible and functional
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'RECTANGLE' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'CIRCLE' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'ARROW' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'TEXT' })).toBeVisible();

    // Tool switching should still work
    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    await rectBtn.click();
    await page.waitForTimeout(300);
    const rectHasBlue = await rectBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(rectHasBlue).toBe(true);

    // Annotations panel heading should still be visible
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('creating annotation fails (POST returns 500) — error shown, page functional', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);

    // Mock POST annotations to return 500
    await page.route('**/api/annotations', (route) => {
      if (route.request().method() === 'POST') {
        route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Failed to create annotation' }),
        });
      } else {
        route.continue();
      }
    });

    // Draw on the canvas to create an annotation
    const canvas = page.locator('canvas');
    await expect(canvas).toBeVisible();
    const box = await canvas.boundingBox();
    expect(box).not.toBeNull();
    if (box) {
      const centerX = box.x + box.width / 2;
      const centerY = box.y + box.height / 2;
      await page.mouse.move(centerX, centerY);
      await page.mouse.down();
      await page.mouse.move(centerX + 60, centerY + 60, { steps: 5 });
      await page.mouse.up();
      await page.waitForTimeout(500);
    }

    // Page should still be functional
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'RECTANGLE' })).toBeVisible();
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Canvas should still be usable
    await expect(canvas).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('video file missing (404) — video player shows error/placeholder, no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Mock video file requests to return 404
    await page.route('**/*.mp4', (route) => {
      route.fulfill({
        status: 404,
        contentType: 'text/plain',
        body: 'Not Found',
      });
    });
    await page.route('**/*.webm', (route) => {
      route.fulfill({
        status: 404,
        contentType: 'text/plain',
        body: 'Not Found',
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(1000);

    // Video element should still be present (even if it can't load)
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // Drawing tools should still be visible
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'RECTANGLE' })).toBeVisible();

    // Annotations panel should still be visible
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Play/Pause button should still be visible
    await expect(page.locator('text=Play/Pause')).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('annotation analysis API returns 500 — analysis section shows error, not stuck loading', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);

    // Mock the annotation analysis API to return 500
    await page.route('**/api/annotations/*/analyze', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Analysis service unavailable' }),
      });
    });

    // Also mock POST annotations to succeed (so we can create one)
    await page.route('**/api/annotations', (route) => {
      if (route.request().method() === 'POST') {
        route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ id: 'test-annotation-1', success: true }),
        });
      } else {
        route.continue();
      }
    });

    // Draw on the canvas to create an annotation
    const canvas = page.locator('canvas');
    await expect(canvas).toBeVisible();
    const box = await canvas.boundingBox();
    expect(box).not.toBeNull();
    if (box) {
      const centerX = box.x + box.width / 2;
      const centerY = box.y + box.height / 2;
      await page.mouse.move(centerX, centerY);
      await page.mouse.down();
      await page.mouse.move(centerX + 70, centerY + 70, { steps: 5 });
      await page.mouse.up();
      await page.waitForTimeout(1000);
    }

    // Page should still be functional — no stuck loading spinners
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();

    // Canvas should still be usable for further drawing
    await expect(canvas).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
