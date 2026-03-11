import { test, expect } from '@playwright/test';
import { buildMockRenderStatus, loadActiveProjectFixture } from './helpers/project-fixtures';

const ACTIVE_PROJECT = loadActiveProjectFixture();
const PROJECT_SECTIONS = ACTIVE_PROJECT.sections;

test.describe('Stage 9: Render & Stitch', () => {
  test.beforeEach(async ({ page }) => {
    await page.route('**/api/pipeline/render/status', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(buildMockRenderStatus()),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Render stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
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
    const select = page.getByTestId('render-mode-select');
    await expect(select).toBeVisible();

    // Check options
    const options = select.locator('option');
    await expect(options).toHaveCount(3);
    await expect(options.nth(0)).toHaveText('All');
    await expect(options.nth(1)).toHaveText('Missing');
    await expect(options.nth(2)).toHaveText('Selected');
  });

  test('render mode selector text is readable (dark theme fix)', async ({ page }) => {
    const select = page.getByTestId('render-mode-select');
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
    const select = page.getByTestId('render-mode-select');
    await select.selectOption('missing');
    await expect(select).toHaveValue('missing');
    await select.selectOption('selected');
    await expect(select).toHaveValue('selected');
    await select.selectOption('all');
    await expect(select).toHaveValue('all');
  });

  test('displays Render button', async ({ page }) => {
    await expect(page.getByTestId('render-sections-button')).toBeVisible();
  });

  test('displays Stitch Full Video button', async ({ page }) => {
    await expect(page.getByTestId('stitch-full-video-button')).toBeVisible();
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

  test('section renders table shows all project sections', async ({ page }) => {
    const rows = page.locator('tbody tr');
    await expect(rows).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('section IDs are visible in table (dark theme fix)', async ({ page }) => {
    // After fix, section IDs should use explicit dark text color
    const firstSectionCell = page.locator('tbody tr').first().locator('td').nth(1);
    await expect(firstSectionCell).toBeVisible();
    await expect(firstSectionCell).toContainText(PROJECT_SECTIONS[0].id);

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
    await expect(checkboxes).toHaveCount(PROJECT_SECTIONS.length);
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
    // Rendered sections use title="Preview", missing sections use title="Not yet rendered"
    const previewButtons = page.locator('tbody tr button[title="Preview"], tbody tr button[title="Not yet rendered"]');
    await expect(previewButtons).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('each row has a re-render button', async ({ page }) => {
    const rerenderButtons = page.locator('tbody tr button[title="Re-render"]');
    await expect(rerenderButtons).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('render status badges are visible', async ({ page }) => {
    await expect(page.locator('tbody tr')).toHaveCount(PROJECT_SECTIONS.length);
    const statusBadges = page.locator('tbody span.rounded-full');
    expect(await statusBadges.count()).toBeGreaterThanOrEqual(1);
    await expect(page.locator('tbody span.rounded-full', { hasText: 'Rendered' }).first()).toBeVisible();
    if (PROJECT_SECTIONS.length > 1) {
      await expect(page.locator('tbody span.rounded-full', { hasText: 'Missing' }).first()).toBeVisible();
    }
  });

  test('progress values are visible for each section', async ({ page }) => {
    await expect(page.locator('tbody tr')).toHaveCount(PROJECT_SECTIONS.length);
    const progressTexts = page.locator('tbody td .text-xs.text-slate-400.mt-1');
    await expect(progressTexts).toHaveCount(PROJECT_SECTIONS.length);
  });

  test('no console errors on load', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(2000);
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
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
    const select = page.getByTestId('render-mode-select');
    await select.selectOption('missing');
    await expect(select).toHaveValue('missing');

    // Click the Render button
    const renderButton = page.getByTestId('render-sections-button');
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

    const stitchButton = page.getByTestId('stitch-full-video-button');
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

    // The modal overlay should appear with the first section ID
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
    expect(capturedBody.sections[0]).toBe(PROJECT_SECTIONS[0].id);
  });

  test('Multiple checkboxes can be toggled independently', async ({ page }) => {
    const checkboxes = page.locator('tbody tr input[type="checkbox"]');
    await expect(checkboxes).toHaveCount(PROJECT_SECTIONS.length);

    const firstCheckbox = checkboxes.nth(0);
    await firstCheckbox.check();
    await expect(firstCheckbox).toBeChecked();

    if (PROJECT_SECTIONS.length > 1) {
      const secondCheckbox = checkboxes.nth(1);
      await secondCheckbox.check();
      await expect(secondCheckbox).toBeChecked();
      await firstCheckbox.uncheck();
      await expect(firstCheckbox).not.toBeChecked();
      await expect(secondCheckbox).toBeChecked();
    } else {
      await firstCheckbox.uncheck();
      await expect(firstCheckbox).not.toBeChecked();
    }
  });

  // ── Bug regression tests ──────────────────────────────────────────────────

  test('Bug #4: POST /api/pipeline/render/run returns JSON (not SSE stream)', async ({ page }) => {
    // The endpoint must return application/json so the frontend can call res.json()
    const result = await page.evaluate(async () => {
      const response = await fetch('/api/pipeline/render/run', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ sections: [] }),
      });
      return {
        contentType: response.headers.get('content-type') ?? '',
        status: response.status,
      };
    });
    expect(result.contentType).toContain('application/json');
    // Empty sections may error (500) but must still return JSON, not SSE
    expect([200, 500]).toContain(result.status);
  });

  test('Bug #4: Render button does not show JSON parse error', async ({ page }) => {
    // Mock the render status reload to avoid network errors
    await page.route('**/api/pipeline/render/status', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
            { id: 'part1_economics', durationSeconds: 382.18, status: 'done', progress: 100 },
            { id: 'part2_paradigm_shift', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'part3_mold', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'part4_precision', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'part5_compound', durationSeconds: 0, status: 'missing', progress: 0 },
            { id: 'closing', durationSeconds: 0, status: 'missing', progress: 0 },
          ],
          fullVideo: { exists: false },
        }),
      });
    });

    const renderButton = page.getByTestId('render-sections-button');
    await renderButton.click();
    await page.waitForTimeout(1500);

    // Must NOT show a JSON parse error
    await expect(page.locator('text=not valid JSON')).not.toBeVisible();
    await expect(page.locator('text=Unexpected token')).not.toBeVisible();
  });

  test('Bug #5: GET /api/pipeline/render/stream endpoint exists and returns SSE', async ({ page }) => {
    const result = await page.evaluate(async () => {
      const response = await fetch('/api/pipeline/render/stream?jobId=nonexistent-job-id');
      return {
        status: response.status,
        contentType: response.headers.get('content-type') ?? '',
      };
    });
    // Should not be 404
    expect(result.status).not.toBe(404);
    expect(result.contentType).toContain('text/event-stream');
  });

  test('Bug #6: "Open in Review →" navigates to Review tab, not Stage 10 Audit', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();

    const openInReviewBtn = page.locator('button', { hasText: 'Open in Review' });
    await openInReviewBtn.click();
    await page.waitForTimeout(500);

    // Must NOT navigate to Stage 10 Audit
    await expect(page.locator('text=Audit Results')).not.toBeVisible();

    // Review tab button should be active (has active styling)
    const reviewTabBtn = page.locator('button').filter({ hasText: /^Review$/ });
    await expect(reviewTabBtn).toHaveCSS('color', 'rgb(255, 255, 255)');
  });

  test('Bug #7: Preview button is disabled for Missing sections', async ({ page }) => {
    // Mock status so row 0 is "done" and row 1 is "missing"
    await page.route('**/api/pipeline/render/status', async (route) => {
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            { id: 'cold_open', durationSeconds: 15.29, status: 'done', progress: 100 },
            { id: 'part2_paradigm_shift', durationSeconds: 0, status: 'missing', progress: 0 },
          ],
          fullVideo: { exists: false },
        }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('button').filter({ hasText: /^9\s*Render/ }).click();
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible({ timeout: 15000 });

    // Row 0 (done) — preview button should be enabled (title="Preview")
    const donePreviewBtn = page.locator('tbody tr').nth(0).locator('td').nth(5).locator('button');
    await expect(donePreviewBtn).not.toBeDisabled();

    // Row 1 (missing) — preview button should be disabled
    const missingPreviewBtn = page.locator('tbody tr').nth(1).locator('td').nth(5).locator('button');
    await expect(missingPreviewBtn).toBeDisabled();

    // Clicking the disabled button must NOT open the modal
    await missingPreviewBtn.click({ force: true });
    await page.waitForTimeout(300);
    await expect(page.locator('text=Preview —')).not.toBeVisible();
  });

  test('Bug #8: Pipeline/Review tab bar stays visible after scrolling', async ({ page }) => {
    // Navigate to Stage 9 (beforeEach already did this)
    await expect(page.locator('h2', { hasText: 'Stage 9' })).toBeVisible();

    // Scroll the window (body-level) to the bottom to expose any layout overflow
    await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
    await page.waitForTimeout(300);

    // The Pipeline and Review tab buttons must still be within the viewport (not scrolled off)
    const pipelineBtn = page.locator('button', { hasText: /^Pipeline$/ });
    const reviewBtn = page.locator('button', { hasText: /^Review$/ });

    const pipelineBox = await pipelineBtn.boundingBox();
    const reviewBox = await reviewBtn.boundingBox();

    expect(pipelineBox).not.toBeNull();
    expect(reviewBox).not.toBeNull();
    // y >= 0 means it is within or below the viewport top
    expect(pipelineBox!.y).toBeGreaterThanOrEqual(0);
    expect(reviewBox!.y).toBeGreaterThanOrEqual(0);
  });
});
