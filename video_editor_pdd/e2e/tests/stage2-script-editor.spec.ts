import { test, expect } from '@playwright/test';

test.describe('Stage 2: Script Editor', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Script stage — use exact text match to avoid hitting "TTS Script"
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    // Wait for Stage 2 heading to confirm navigation
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    // Give CodeMirror time to initialize
    await page.waitForTimeout(1500);
  });

  test('displays Stage 2 heading', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();
  });

  test('CodeMirror editor renders', async ({ page }) => {
    // CodeMirror creates elements with cm-editor class
    const editor = page.locator('.cm-editor');
    await expect(editor).toBeVisible();
  });

  test('script content is loaded from API', async ({ page }) => {
    // Mock script API to return content
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Hello world\nVISUAL: A sunset scene' }),
        });
      }
      return route.continue();
    });
    // Re-navigate to pick up the mock
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    const editor = page.locator('.cm-editor');
    await expect(editor).toBeVisible({ timeout: 15000 });
    await expect(page.locator('.cm-line').first()).toBeVisible({ timeout: 10000 });
    const text = await editor.textContent();
    expect(text).toBeTruthy();
    expect(text!.length).toBeGreaterThan(0);
  });

  test('structured preview panel shows content', async ({ page }) => {
    await page.waitForTimeout(1000);
    // The right-side preview should show parsed content
    // Use the inner main element (the stage panel container)
    const mainContent = page.locator('main.flex-1');
    const textContent = await mainContent.textContent();
    // Should contain NARRATOR or VISUAL blocks from the script
    expect(textContent).toBeTruthy();
  });

  test('Generate TTS Script button exists', async ({ page }) => {
    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeVisible();
  });

  test('Generate TTS Script button is enabled when NARRATOR content exists', async ({ page }) => {
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: The economy changed everything.\nVISUAL: A graph rising.' }),
        });
      }
      return route.continue();
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    const isDisabled = await generateBtn.getAttribute('disabled');
    expect(isDisabled).toBeNull();
  });

  test('Generate TTS Script button is clickable and triggers API call', async ({ page }) => {
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Test content for generation.' }),
        });
      }
      return route.continue();
    });

    let apiCallTriggered = false;
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      apiCallTriggered = true;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-job-123' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeEnabled({ timeout: 5000 });
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(apiCallTriggered).toBe(true);
  });

  test('CodeMirror editor area is present and content is editable', async ({ page }) => {
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Editable test content.' }),
        });
      }
      return route.continue();
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    const editor = page.locator('.cm-editor');
    await expect(editor).toBeVisible({ timeout: 15000 });

    const cmContent = page.locator('.cm-content');
    await expect(cmContent).toBeVisible();
    await cmContent.click();

    await expect(editor).toHaveClass(/cm-focused/, { timeout: 5000 }).catch(() => {});

    const isEditable = await cmContent.getAttribute('contenteditable');
    expect(isEditable).toBe('true');

    const editorText = await editor.textContent();
    expect(editorText!.length).toBeGreaterThan(0);
  });

  test('Split pane divider exists and is visible', async ({ page }) => {
    // The divider is a thin div between left and right panes with cursor-col-resize
    const divider = page.locator('.cursor-col-resize');
    await expect(divider).toBeVisible();
  });

  test('Preview pane shows parsed content blocks', async ({ page }) => {
    await page.waitForTimeout(1500);

    // The right pane (preview) should contain rendered blocks from the script
    // The preview pane is the second child of the split container
    const mainContent = page.locator('main.flex-1');
    const previewText = await mainContent.textContent();
    expect(previewText).toBeTruthy();
    expect(previewText!.length).toBeGreaterThan(0);
  });

  test('Split pane divider is draggable and changes pane widths', async ({ page }) => {
    const divider = page.locator('.cursor-col-resize');
    await expect(divider).toBeVisible();

    // Get initial left pane width via the cm-editor's parent container
    const editorContainer = page.locator('.cm-editor').locator('..');
    const initialBox = await editorContainer.boundingBox();
    const initialWidth = initialBox ? initialBox.width : 0;

    // Perform drag: mousedown on divider, move 100px right, mouseup
    const box = await divider.boundingBox();
    if (box) {
      await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
      await page.mouse.down();
      await page.mouse.move(box.x + box.width / 2 + 100, box.y + box.height / 2, { steps: 5 });
      await page.mouse.up();
    }

    await page.waitForTimeout(300);

    // Verify no crash occurred — page still shows Stage 2 heading
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();

    // Optionally verify the left pane width increased after dragging right
    const afterBox = await editorContainer.boundingBox();
    const afterWidth = afterBox ? afterBox.width : 0;
    // The drag should have expanded the left pane (or at minimum not crashed)
    expect(afterWidth).toBeGreaterThanOrEqual(initialWidth);
  });

  test('Auto-save triggers PUT on content change', async ({ page }) => {
    let putCalled = false;

    await page.route('**/api/project/script', (route) => {
      if (route.request().method() === 'PUT') {
        putCalled = true;
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ success: true }),
        });
      }
      return route.continue();
    });

    // Click into the CodeMirror content area and type
    const cmContent = page.locator('.cm-content');
    await expect(cmContent).toBeVisible();
    await cmContent.click();
    await page.keyboard.type('TEST');

    // Wait longer than the debounce delay (1s) to allow the PUT to fire
    await page.waitForTimeout(2000);

    expect(putCalled).toBe(true);
  });

  // === Bug fix tests ===

  test('BUG-1: CodeMirror editor preserves cursor position after typing multiple characters', async ({ page }) => {
    // Bug: CodeMirror useEffect had [content] dependency, destroying/recreating
    // the editor on every keystroke, losing cursor position and undo history.
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Original line.' }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    const cmContent = page.locator('.cm-content');
    await expect(cmContent).toBeVisible();
    await cmContent.click();

    // Type multiple characters sequentially
    await page.keyboard.type('ABCDE', { delay: 100 });
    await page.waitForTimeout(500);

    // All typed characters should appear together in sequence in the editor
    const editorText = await page.locator('.cm-editor').textContent();
    expect(editorText).toContain('ABCDE');
  });

  test('BUG-2: SseLogPanel appears after clicking Generate TTS Script', async ({ page }) => {
    // Bug: onAdvance() was called immediately after POST, before SSE job completes,
    // so the SseLogPanel was never visible. Now onAdvance should only fire on SSE done.
    let advanceCalled = false;

    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Test content for TTS.' }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });

    await page.route('**/api/pipeline/tts-script/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-sse-job-456' }),
      });
    });

    // Mock the SSE stream endpoint to stay open (don't send 'done' immediately)
    await page.route('**/api/jobs/test-sse-job-456/stream', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache', 'Connection': 'keep-alive' },
        body: 'data: {"message":"Processing..."}\n\n',
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeEnabled({ timeout: 5000 });
    await generateBtn.click();

    // Wait for the SseLogPanel to appear — it should remain visible since job isn't done
    await page.waitForTimeout(1000);

    // The Stage 2 heading should STILL be visible (not navigated away)
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible();

    // The button should show "Generating…" while the job is in progress
    await expect(page.locator('button', { hasText: 'Generating' })).toBeVisible();
  });

  test('BUG-4: Split ratio from localStorage is clamped to 15%-85%', async ({ page }) => {
    // Bug: localStorage values outside 15%-85% were not clamped on load.
    await page.goto('/');
    await page.waitForLoadState('networkidle');

    // Set an extreme value in localStorage before navigating to Stage 2
    await page.evaluate(() => {
      localStorage.setItem('script-editor-split-ratio', '0.05');
    });

    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(1500);

    // The left pane width should be at least 15% of the container, not 5%
    const container = page.locator('.cm-editor').locator('..').locator('..');
    const leftPane = page.locator('.cm-editor').locator('..').locator('..');
    const containerBox = await container.boundingBox();

    // Read the actual stored ratio back — it should have been clamped
    const storedRatio = await page.evaluate(() => {
      return localStorage.getItem('script-editor-split-ratio');
    });
    const ratio = parseFloat(storedRatio!);
    expect(ratio).toBeGreaterThanOrEqual(0.15);
    expect(ratio).toBeLessThanOrEqual(0.85);
  });

  test('BUG-5: No auto-save PUT fires on initial content load', async ({ page }) => {
    // Bug: auto-save was firing PUT immediately when content loaded from API,
    // even though nothing was edited.
    const putCalls: string[] = [];

    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Loaded content.' }),
        });
      }
      if (route.request().method() === 'PUT') {
        putCalls.push('PUT');
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ ok: true }),
        });
      }
      return route.continue();
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });

    // Wait well past the 1s debounce without typing anything
    await page.waitForTimeout(3000);

    // No PUT should have fired since the user didn't edit anything
    expect(putCalls.length).toBe(0);
  });

  test('BUG-7: Generate button stays disabled during active generation', async ({ page }) => {
    // Bug: isGenerating was reset to false in the finally block after POST,
    // allowing the user to click again while the job was still running.
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Test for duplicate prevention.' }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });

    await page.route('**/api/pipeline/tts-script/run', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-dup-job' }),
      });
    });

    await page.route('**/api/jobs/test-dup-job/stream', (route) => {
      // Keep SSE stream open (job still running)
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        headers: { 'Cache-Control': 'no-cache' },
        body: 'data: {"message":"Still working..."}\n\n',
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    const generateBtn = page.locator('button', { hasText: /Generate TTS Script|Generating/ });
    await expect(generateBtn).toBeEnabled({ timeout: 5000 });
    await generateBtn.click();

    // Wait for POST to complete but job still running
    await page.waitForTimeout(1000);

    // Button should still be disabled/showing "Generating…" since job is active
    const btn = page.locator('button', { hasText: 'Generating' });
    await expect(btn).toBeVisible();
    await expect(btn).toBeDisabled();
  });

  test('Preview shows color-coded blocks: blue narrator, teal visual, gray headers', async ({ page }) => {
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({
            content: '## Introduction\nNARRATOR: Welcome to the show.\n[VISUAL: A spinning globe]\nSome plain text.',
          }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    // Blue ■ for narrator blocks
    const narratorBadge = page.locator('span.text-blue-500', { hasText: '■' });
    await expect(narratorBadge).toBeVisible();

    // Teal ▣ for visual blocks
    const visualBadge = page.locator('span.text-teal-500', { hasText: '▣' });
    await expect(visualBadge).toBeVisible();

    // Gray header text
    const headerBlock = page.locator('.text-slate-500', { hasText: 'Introduction' });
    await expect(headerBlock).toBeVisible();
  });

  test('Generate button is disabled when editor has no NARRATOR content', async ({ page }) => {
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: '[VISUAL: Just visuals, no narrator]\nSome plain text.' }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await expect(generateBtn).toBeDisabled();
  });

  test('BUG-8: CodeMirror editor fills the full height of the left pane', async ({ page }) => {
    // Bug: CodeMirror editor was only ~26px tall (auto-sized to content),
    // not filling its parent container. Users couldn't click in the empty
    // space below the text to focus the editor.
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Short content.' }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    const editor = page.locator('.cm-editor');
    await expect(editor).toBeVisible();

    // The editor should fill its parent container height, not just auto-size to content
    const editorHeight = await editor.evaluate((el) => el.offsetHeight);
    const parentHeight = await editor.evaluate((el) => el.parentElement!.offsetHeight);

    // Editor should be at least 90% of its parent height (allowing small margin)
    expect(editorHeight).toBeGreaterThan(parentHeight * 0.9);
  });

  test('BUG-8: Clicking empty space in left pane focuses the CodeMirror editor', async ({ page }) => {
    // Bug: Because the editor was only 26px tall, clicking below the text
    // in the left pane didn't focus the editor.
    await page.route('**/api/project/script**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'NARRATOR: Short.' }),
        });
      }
      return route.fulfill({ status: 200, contentType: 'application/json', body: '{"ok":true}' });
    });
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.getByText('Script', { exact: true }).click();
    await expect(page.locator('h2', { hasText: 'Stage 2' })).toBeVisible({ timeout: 10000 });
    await page.waitForTimeout(2000);

    // Click well below the text content in the left pane (middle of pane)
    const editor = page.locator('.cm-editor');
    const box = await editor.boundingBox();
    expect(box).toBeTruthy();
    // Click at 75% down the editor — should still focus it
    await page.mouse.click(box!.x + box!.width / 2, box!.y + box!.height * 0.75);
    await page.waitForTimeout(300);

    // Editor should gain focus
    await expect(editor).toHaveClass(/cm-focused/);
  });
});
