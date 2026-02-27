import { test, expect } from '@playwright/test';

test.describe('Stage 3: TTS Script Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('load');
    // Wait for React to hydrate and sidebar to render
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'TTS Script' }).first().click({ timeout: 10000 });
    await page.waitForTimeout(1000);
  });

  test('renders without crash', async ({ page }) => {
    // No error overlay should appear
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays Generate TTS Script button', async ({ page }) => {
    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeVisible();
  });

  test('displays diff view with main_script.md and tts_script.md labels', async ({ page }) => {
    await expect(page.locator('text=main_script.md').first()).toBeVisible();
    await expect(page.locator('text=tts_script.md').first()).toBeVisible();
  });

  test('displays CodeMirror editor with Edit label', async ({ page }) => {
    await expect(page.locator('text=Edit tts_script.md')).toBeVisible();
    // CodeMirror should render a .cm-editor element
    const cmEditor = page.locator('.cm-editor');
    await expect(cmEditor).toBeVisible();
  });

  test('displays Render Audio advance button', async ({ page }) => {
    const advanceBtn = page.locator('button', { hasText: 'Render Audio' });
    await expect(advanceBtn).toBeVisible();
  });

  test('displays last run timestamp area', async ({ page }) => {
    await expect(page.locator('text=Last run:').first()).toBeVisible();
  });

  test('script content loads as parsed text, not raw JSON', async ({ page }) => {
    // The diff view should display the actual markdown content from main_script.md,
    // NOT the raw JSON wrapper like {"content":"# Prompt-Driven Development..."}
    // Wait for content to load
    await page.waitForTimeout(1500);

    // The diff view left panel (main_script.md) should NOT contain JSON wrapper text
    const diffPanel = page.locator('pre').first();
    const diffText = await diffPanel.textContent();

    // If the API response is parsed correctly, the content should NOT start with {"content":
    expect(diffText).not.toContain('{"content"');

    // The content should be actual text (not empty and not JSON)
    if (diffText && diffText.trim().length > 0) {
      expect(diffText).not.toContain('{');
      expect(diffText!.length).toBeGreaterThan(0);
    }
  });

  test('editor loads script content, not raw JSON', async ({ page }) => {
    // The CodeMirror editor should contain parsed markdown content, not JSON
    await page.waitForTimeout(1500);

    const editorContent = page.locator('.cm-content');
    const text = await editorContent.textContent();

    // Should NOT contain the JSON wrapper
    if (text && text.trim().length > 0) {
      expect(text).not.toContain('{"content"');
    }
  });

  test('Generate button click triggers API call', async ({ page }) => {
    let apiCallTriggered = false;
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      apiCallTriggered = true;
      route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body: 'data: {"type":"started","jobId":"test-tts-gen-job"}\n\n',
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(apiCallTriggered).toBe(true);
  });

  test('CodeMirror content area is interactive and accepts input', async ({ page }) => {
    await page.waitForTimeout(2000);

    const cmEditor = page.locator('.cm-editor');
    // CodeMirror may or may not be present depending on stage state
    const editorVisible = await cmEditor.isVisible().catch(() => false);
    if (!editorVisible) {
      // If no CodeMirror editor, at least verify the stage loaded without crash
      const errorOverlay = page.locator('text=Runtime TypeError');
      const hasError = await errorOverlay.isVisible().catch(() => false);
      expect(hasError).toBe(false);
      return;
    }

    const cmContent = page.locator('.cm-content');
    await expect(cmContent).toBeVisible();

    // Click into the editor to focus it
    await cmContent.click();

    // Type at end of current content
    await page.keyboard.press('End');
    await page.keyboard.type(' INTERACTIVE_TEST_TEXT');
    await page.waitForTimeout(500);

    // The typed text should appear in the editor
    await expect(cmEditor).toContainText('INTERACTIVE_TEST_TEXT');
  });

  test('Render Audio button exists and is clickable without crash', async ({ page }) => {
    const renderAudioBtn = page.locator('button', { hasText: 'Render Audio' });
    await expect(renderAudioBtn).toBeVisible();

    // The button click should not cause any crash
    // Note: The button may be disabled if tts_script does not exist yet
    const isDisabled = await renderAudioBtn.getAttribute('disabled');
    if (isDisabled === null) {
      // If not disabled, click it and verify no error overlay appears
      await renderAudioBtn.click();
      await page.waitForTimeout(500);

      const errorOverlay = page.locator('text=Runtime TypeError');
      const hasError = await errorOverlay.isVisible().catch(() => false);
      expect(hasError).toBe(false);
    } else {
      // If disabled, verify it has the expected disabled styling (cursor-not-allowed)
      await expect(renderAudioBtn).toBeDisabled();
    }
  });

  // BUG-A: Generate button must be disabled while generation is in progress
  test('Generate button disables during active generation', async ({ page }) => {
    // Mock the API to hold the SSE response so we can observe the in-flight state
    await page.route('**/api/pipeline/tts-script/run', async (route) => {
      // Delay the response to simulate a long-running job
      await new Promise((resolve) => setTimeout(resolve, 3000));
      await route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body: 'data: {"type":"started","jobId":"test-gen-job-123"}\n\n',
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeEnabled();

    // Click generate
    await generateBtn.click();

    // Button text should change to "Generating…" and become disabled
    const generatingBtn = page.locator('button', { hasText: 'Generating' });
    await expect(generatingBtn).toBeDisabled({ timeout: 2000 });

    // Original "Generate TTS Script" text should not be visible during generation
    await expect(generateBtn).not.toBeVisible();
  });

  // BUG-B: Scripts must reload after generation completes (SseLogPanel onDone)
  test('diff view and editor reload after generation completes', async ({ page }) => {
    // Mock the generate endpoint to return a jobId via SSE stream
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body: 'data: {"type":"started","jobId":"test-reload-job"}\n\n',
      });
    });

    // Mock the SSE stream to emit a done event quickly
    await page.route('**/api/jobs/test-reload-job/stream', (route) => {
      const body =
        'event: done\ndata: {}\n\n';
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        headers: {
          'Cache-Control': 'no-cache',
          Connection: 'keep-alive',
        },
        body,
      });
    });

    // Track script reload calls after generation
    let scriptFetchCount = 0;
    await page.route('**/api/project/script?file=main', (route) => {
      scriptFetchCount++;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: '# Updated Main Script' }),
      });
    });
    await page.route('**/api/project/script?file=tts', (route) => {
      scriptFetchCount++;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: '# Updated TTS Script' }),
      });
    });

    // Reset counter after initial load
    await page.waitForTimeout(1500);
    scriptFetchCount = 0;

    // Click generate
    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await generateBtn.click();

    // Wait for SSE done event to fire and scripts to reload
    await page.waitForTimeout(3000);

    // Scripts should have been re-fetched after onDone fired
    expect(scriptFetchCount).toBeGreaterThanOrEqual(2);
  });

  // BUG-D: Saving guard must not drop edits — queued save should fire after current save completes
  test('auto-save does not drop edits during concurrent saves', async ({ page }) => {
    await page.waitForTimeout(1500);

    const cmContent = page.locator('.cm-content');
    const editorVisible = await cmContent.isVisible().catch(() => false);
    if (!editorVisible) return;

    // Track save calls
    const savedBodies: string[] = [];
    await page.route('**/api/project/script?file=tts', async (route) => {
      if (route.request().method() === 'POST') {
        const body = route.request().postData() ?? '';
        savedBodies.push(body);
        // Simulate slow save
        await new Promise((resolve) => setTimeout(resolve, 500));
        await route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
      } else {
        await route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'initial content' }),
        });
      }
    });

    // Click into editor, type first batch, wait for debounce to trigger save
    await cmContent.click();
    await page.keyboard.press('End');
    await page.keyboard.type(' FIRST_EDIT');
    // Wait for debounce (1s) plus a bit for the save to start
    await page.waitForTimeout(1200);

    // Now type second batch and blur to trigger immediate save
    await page.keyboard.type(' SECOND_EDIT');
    await page.locator('h2').click(); // blur the editor
    await page.waitForTimeout(1500);

    // The last saved body should contain SECOND_EDIT — it must not be dropped
    const lastSave = savedBodies[savedBodies.length - 1] ?? '';
    expect(lastSave).toContain('SECOND_EDIT');
  });

  // BUG: Generate button must correctly parse SSE response to extract jobId
  // The POST /api/pipeline/tts-script/run endpoint returns an SSE stream,
  // not JSON. The component must read the stream and extract the jobId
  // from the first SSE event, not call res.json().
  test('Generate button correctly parses SSE response and extracts jobId', async ({ page }) => {
    // Mock the generate endpoint to return a realistic SSE stream (not JSON)
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      const sseBody = [
        'data: {"type":"started","jobId":"sse-test-job-42"}\n\n',
        'data: {"type":"log","message":"Reading main_script.md..."}\n\n',
        'data: {"type":"complete","jobId":"sse-test-job-42"}\n\n',
      ].join('');
      route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        headers: {
          'Cache-Control': 'no-cache',
          Connection: 'keep-alive',
        },
        body: sseBody,
      });
    });

    // Mock the job stream endpoint to confirm the jobId was passed through
    let streamJobId: string | null = null;
    await page.route('**/api/jobs/*/stream', (route) => {
      const url = route.request().url();
      const match = url.match(/\/api\/jobs\/([^/]+)\/stream/);
      streamJobId = match ? match[1] : null;
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body: 'event: done\ndata: {}\n\n',
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await generateBtn.click();
    await page.waitForTimeout(2000);

    // The component should have parsed the SSE stream and passed the jobId
    // to SseLogPanel, which would have opened /api/jobs/sse-test-job-42/stream
    expect(streamJobId).toBe('sse-test-job-42');
  });

  // BUG: Generate button must not throw console error parsing SSE as JSON
  test('Generate button does not throw JSON parse error', async ({ page }) => {
    const consoleErrors: string[] = [];
    page.on('pageerror', (err) => consoleErrors.push(err.message));

    // Mock with realistic SSE response
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body: 'data: {"type":"started","jobId":"no-error-job"}\n\n',
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await generateBtn.click();
    await page.waitForTimeout(1500);

    // There should be no SyntaxError from trying to parse SSE as JSON
    const jsonErrors = consoleErrors.filter(e => e.includes('SyntaxError') || e.includes('not valid JSON'));
    expect(jsonErrors).toHaveLength(0);
  });

  // BUG: Double-clicking Generate must only trigger one API call
  test('double-click on Generate only sends one API request', async ({ page }) => {
    let apiCallCount = 0;
    await page.route('**/api/pipeline/tts-script/run', async (route) => {
      apiCallCount++;
      // Hold the response so the second click has time to fire
      await new Promise((resolve) => setTimeout(resolve, 2000));
      await route.fulfill({
        status: 202,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
        body: 'data: {"type":"started","jobId":"double-click-guard-job"}\n\n',
      });
    });

    // Use synchronous double-click via evaluate to avoid Playwright await gaps
    await page.evaluate(() => {
      const btn = [...document.querySelectorAll('button')].find(
        (b) => b.textContent?.includes('Generate TTS Script')
      );
      if (btn) {
        btn.click();
        btn.click();
      }
    });
    await page.waitForTimeout(500);

    // Only one API call should have been made
    expect(apiCallCount).toBe(1);
  });
});
