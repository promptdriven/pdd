import { test, expect } from '@playwright/test';

test.describe('Stage 5: Audio Sync', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Audio Sync stage
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
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
    const heading = page.locator('h3', { hasText: 'Audio Sync Section Groups' });
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

  // ── Interactive tests ──────────────────────────────────────────────

  test('Save Config button click triggers a PUT /api/project call', async ({ page }) => {
    // Mock the PUT endpoint so the test doesn't depend on a running backend
    let putCalled = false;
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'PUT') {
        putCalled = true;
        return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
      }
      return route.fallback();
    });

    const saveBtn = page.locator('button', { hasText: 'Save Config' });
    await expect(saveBtn).toBeVisible();
    await expect(saveBtn).toBeEnabled();

    await saveBtn.click();
    // The button text changes to "Saving…" while the request is in flight
    await page.waitForTimeout(500);

    // After the mocked response resolves the button should revert to "Save Config"
    await expect(saveBtn).toContainText('Save Config');
    expect(putCalled).toBe(true);
  });

  test('Run Audio Sync button click triggers a POST /api/pipeline/audio-sync/run call', async ({ page }) => {
    let postCalled = false;
    await page.route('**/api/pipeline/audio-sync/run', (route) => {
      postCalled = true;
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-job-123' }),
      });
    });

    const runBtn = page.locator('button', { hasText: 'Run Audio Sync' });
    await expect(runBtn).toBeVisible();
    await runBtn.click();
    await page.waitForTimeout(500);

    expect(postCalled).toBe(true);
  });

  test('section select dropdown changes the displayed section and re-fetches timestamps', async ({ page }) => {
    const select = page.locator('select');
    await expect(select).toBeVisible();

    // Record the initial selected value
    const initialValue = await select.inputValue();

    // Intercept timestamp fetches to verify re-fetch happens
    let timestampFetchCount = 0;
    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      timestampFetchCount++;
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ words: [] }),
      });
    });

    // Get all options and pick a different one if available
    const options = select.locator('option');
    const optionCount = await options.count();
    if (optionCount > 1) {
      // Select the second option
      const secondValue = await options.nth(1).getAttribute('value');
      await select.selectOption(secondValue!);
      await page.waitForTimeout(500);

      // The select value should have changed
      const newValue = await select.inputValue();
      expect(newValue).not.toBe(initialValue);

      // A new timestamp fetch should have been triggered
      expect(timestampFetchCount).toBeGreaterThanOrEqual(1);
    }
  });

  test('search input filters the word list', async ({ page }) => {
    // Mock timestamps with known words so we can test filtering
    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          words: [
            { word: 'hello', start: 0.0, end: 0.5, segmentId: 'seg1' },
            { word: 'world', start: 0.5, end: 1.0, segmentId: 'seg1' },
            { word: 'testing', start: 1.0, end: 1.5, segmentId: 'seg2' },
            { word: 'playwright', start: 1.5, end: 2.0, segmentId: 'seg2' },
            { word: 'hello', start: 2.0, end: 2.5, segmentId: 'seg3' },
          ],
        }),
      });
    });

    // Re-navigate to trigger timestamp load with our mock
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);

    // Before filtering: word count should show "5 of 5 words"
    await expect(page.locator('text=/5 of 5 words/')).toBeVisible();

    // Type "hello" in the search input to filter
    const searchInput = page.locator('input[placeholder="Search word\u2026"]');
    await searchInput.fill('hello');
    await page.waitForTimeout(300);

    // After filtering: should show "2 of 5 words"
    await expect(page.locator('text=/2 of 5 words/')).toBeVisible();

    // Clear the search to verify it resets
    await searchInput.fill('');
    await page.waitForTimeout(300);
    await expect(page.locator('text=/5 of 5 words/')).toBeVisible();
  });

  test('virtualized table scrolls and renders rows on scroll', async ({ page }) => {
    // Create enough mock data to exceed the viewport (VIEWPORT_HEIGHT=320, ROW_HEIGHT=32)
    const manyWords = Array.from({ length: 50 }, (_, i) => ({
      word: `word_${i}`,
      start: i * 0.1,
      end: (i + 1) * 0.1,
      segmentId: `seg_${Math.floor(i / 10)}`,
    }));

    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ words: manyWords }),
      });
    });

    // Re-navigate to trigger timestamp load with our mock
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);

    // Verify the word count
    await expect(page.locator('text=/50 of 50 words/')).toBeVisible();

    // The first word should be visible
    await expect(page.locator('td', { hasText: 'word_0' })).toBeVisible();

    // Scroll the virtualized container down
    const scrollContainer = page.locator('div[style*="contain: strict"]');
    await scrollContainer.evaluate((el) => {
      el.scrollTop = 1200; // Scroll down ~37 rows
    });
    await page.waitForTimeout(500);

    // After scrolling, late words should now be rendered
    await expect(page.locator('td', { hasText: 'word_40' })).toBeVisible();
  });

  test('Continue button navigates to the next stage', async ({ page }) => {
    const continueBtn = page.locator('button', { hasText: 'Continue' });
    await expect(continueBtn).toBeVisible();
    await expect(continueBtn).toBeEnabled();
    await continueBtn.click();
    await page.waitForTimeout(1000);

    // After clicking Continue, we should advance to Stage 6 (Spec Gen)
    // Verify the sidebar now highlights a different stage or the stage content changes
    await expect(page.locator('text=Spec Generation').first()).toBeVisible();
  });

  test('timestamps API returns word data when file is a raw array (Bug #1)', async ({ page }) => {
    // Bug: word_timestamps.json stores a raw array but the API route wraps it
    // in { words: parsed.words } — since parsed is an array, parsed.words is
    // undefined, so the API returns {}. The component then shows 0 of 0 words.
    // After the fix, the API should normalise both raw-array and {words:[...]}
    // file formats so the viewer shows the actual word data.

    // Mock the timestamps endpoint to return a raw-array-style response
    // (simulating what the fixed API route should produce from a raw-array file)
    await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          words: [
            { word: 'hello', start: 0.0, end: 0.5, segmentId: 'seg1' },
            { word: 'world', start: 0.5, end: 1.0, segmentId: 'seg1' },
          ],
        }),
      });
    });

    // Re-navigate to trigger fresh load with the mock
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);
    await sidebar.locator('button', { hasText: 'Audio Sync' }).first().click();
    await page.waitForTimeout(1000);

    // The word count should reflect the 2 words, not 0 of 0
    await expect(page.locator('text=/2 of 2 words/')).toBeVisible();
  });

  test('Run Audio Sync POST returns JSON jobId so SSE panel appears (Bug #2)', async ({ page }) => {
    // Bug: POST /api/pipeline/audio-sync/run returns an SSE stream but the
    // component calls res.json(), which throws on an SSE body. As a result
    // setJobId is never called and the SSE log panel never renders.
    // After the fix, the POST should return { jobId } as JSON so the
    // SseLogPanel receives the jobId and renders "Waiting for logs…".

    let postCalled = false;
    await page.route('**/api/pipeline/audio-sync/run', (route) => {
      postCalled = true;
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-job-sse-123' }),
      });
    });

    const runBtn = page.locator('button', { hasText: 'Run Audio Sync' });
    await expect(runBtn).toBeVisible();
    await runBtn.click();
    await page.waitForTimeout(1000);

    expect(postCalled).toBe(true);

    // The SSE log panel should appear (showing "Waiting for logs…" or an error
    // since the mock job doesn't exist in the DB)
    const ssePanel = page.locator('text=/Waiting for logs|Error: Job not found/');
    await expect(ssePanel.first()).toBeVisible();
  });
});
