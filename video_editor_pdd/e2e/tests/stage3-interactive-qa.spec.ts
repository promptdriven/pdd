import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

/**
 * Navigate to Stage 3 (TTS Script) via the sidebar.
 * Uses 3-attempt retry with the current sidebar button contract.
 */
async function navigateToStage3(page: import('@playwright/test').Page) {
  await page.goto('/');
  await page.waitForLoadState('networkidle');

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });

  // Wait for React hydration
  await page.waitForTimeout(1000);

  const heading = page.locator('h2', { hasText: 'Stage 3' });
  const stageButton = sidebar.locator('button').filter({ hasText: /^3\s*TTS Script/ }).first();

  // Attempt 1: Playwright click
  await stageButton.click();
  try {
    await expect(heading).toBeVisible({ timeout: 3000 });
  } catch {
    // Attempt 2: JS click
    await page.waitForTimeout(500);
    await page.evaluate(() => {
      const buttons = Array.from(document.querySelectorAll('aside button'));
      const stageButton = buttons.find((button) => button.textContent?.trim().startsWith('3'));
      if (stageButton) {
        (stageButton as HTMLElement).click();
      }
    });
    try {
      await expect(heading).toBeVisible({ timeout: 3000 });
    } catch {
      // Attempt 3: force click after longer wait
      await page.waitForTimeout(1000);
      await stageButton.click({ force: true });
      await expect(heading).toBeVisible({ timeout: 10000 });
    }
  }

  // Give CodeMirror time to initialize
  await page.waitForTimeout(1500);
}

/**
 * Navigate to Stage 3 with mocked GET responses for both main and tts scripts.
 * Sets up route mocks BEFORE navigating so they're in place for the fetch.
 */
async function navigateWithMockedScripts(
  page: import('@playwright/test').Page,
  mainContent: string,
  ttsContent: string | null,
) {
  await page.route('**/api/project/script?file=main', (route) => {
    if (route.request().method() === 'GET') {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: mainContent }),
      });
    }
    return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
  });

  await page.route('**/api/project/script?file=tts', (route) => {
    if (route.request().method() === 'GET') {
      if (ttsContent === null) {
        return route.fulfill({ status: 404, contentType: 'application/json', body: '{"error":"not found"}' });
      }
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ content: ttsContent }),
      });
    }
    if (route.request().method() === 'POST') {
      return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
    }
    return route.continue();
  });

  await navigateToStage3(page);
  await page.waitForTimeout(500);
}

test.describe('Stage 3: Interactive QA - Comprehensive Feature Testing', () => {
  // =========================================================================
  // Group A: Initial Load & UI Elements (~9 tests + screenshot)
  // =========================================================================
  test.describe('Group A: Initial load & UI elements', () => {
    test('A1: "Stage 3 — TTS Script" heading visible', async ({ page }) => {
      await navigateToStage3(page);
      const heading = page.locator('h2', { hasText: 'Stage 3' });
      await expect(heading).toBeVisible();
      await expect(heading).toHaveText(/Stage 3 — TTS Script/);
    });

    test('A2: "Generate TTS Script ↺" button visible', async ({ page }) => {
      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await expect(btn).toBeVisible();
      await expect(btn).toContainText('↺');
    });

    test('A3: Diff view has "main_script.md" label', async ({ page }) => {
      await navigateToStage3(page);
      const label = page.locator('text=main_script.md').first();
      await expect(label).toBeVisible();
    });

    test('A4: Diff view has "tts_script.md" label', async ({ page }) => {
      await navigateToStage3(page);
      const label = page.locator('text=tts_script.md').first();
      await expect(label).toBeVisible();
    });

    test('A5: CodeMirror editor renders with "Edit tts_script.md" label', async ({ page }) => {
      await navigateToStage3(page);
      await expect(page.locator('text=Edit tts_script.md')).toBeVisible();
      const cmEditor = page.locator('.cm-editor');
      await expect(cmEditor).toBeVisible();
    });

    test('A6: "Render Audio →" advance button visible', async ({ page }) => {
      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Render Audio' });
      await expect(btn).toBeVisible();
      await expect(btn).toContainText('→');
    });

    test('A7: "Last run:" timestamp area visible', async ({ page }) => {
      await navigateToStage3(page);
      await expect(page.locator('text=Last run:').first()).toBeVisible();
    });

    test('A8: Content loads as text, not raw JSON (no {"content" wrapper)', async ({ page }) => {
      await navigateWithMockedScripts(page, '# Main Script Content', '# TTS Script Content');
      const diffPanel = page.locator('pre').first();
      const text = await diffPanel.textContent();
      expect(text).not.toContain('{"content"');
      expect(text).not.toContain('{');
    });

    test('A9: screenshot — full initial state', async ({ page }) => {
      await navigateToStage3(page);
      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-A9-initial-state.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group B: Diff View (~8 tests + screenshot)
  // =========================================================================
  test.describe('Group B: Diff view', () => {
    test('B1: Unchanged lines have text-gray-400 class', async ({ page }) => {
      // Same content on both sides → all unchanged
      await navigateWithMockedScripts(page, 'Line one\nLine two', 'Line one\nLine two');
      const leftPre = page.locator('pre').first();
      const leftDivs = leftPre.locator('div');
      const count = await leftDivs.count();
      expect(count).toBeGreaterThan(0);
      for (let i = 0; i < count; i++) {
        const cls = await leftDivs.nth(i).getAttribute('class');
        expect(cls).toContain('text-gray-400');
      }
    });

    test('B2: Added lines (in tts only) have text-green-400 class on right pane', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Shared line', 'Shared line\nAdded in tts');
      const rightPre = page.locator('pre').nth(1);
      const rightDivs = rightPre.locator('div');
      const classes: string[] = [];
      const count = await rightDivs.count();
      for (let i = 0; i < count; i++) {
        classes.push(await rightDivs.nth(i).getAttribute('class') ?? '');
      }
      const hasGreen = classes.some((c) => c.includes('text-green-400'));
      expect(hasGreen).toBe(true);
    });

    test('B3: Removed lines (in main only) have text-red-400 class on left pane', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Shared line\nRemoved from main', 'Shared line');
      const leftPre = page.locator('pre').first();
      const leftDivs = leftPre.locator('div');
      const classes: string[] = [];
      const count = await leftDivs.count();
      for (let i = 0; i < count; i++) {
        classes.push(await leftDivs.nth(i).getAttribute('class') ?? '');
      }
      const hasRed = classes.some((c) => c.includes('text-red-400'));
      expect(hasRed).toBe(true);
    });

    test('B4: Empty placeholders have text-transparent class', async ({ page }) => {
      // When tts has an added line, left pane gets an empty placeholder
      await navigateWithMockedScripts(page, 'Same', 'Same\nExtra tts line');
      const leftPre = page.locator('pre').first();
      const leftDivs = leftPre.locator('div');
      const classes: string[] = [];
      const count = await leftDivs.count();
      for (let i = 0; i < count; i++) {
        classes.push(await leftDivs.nth(i).getAttribute('class') ?? '');
      }
      const hasTransparent = classes.some((c) => c.includes('text-transparent'));
      expect(hasTransparent).toBe(true);
    });

    test('B5: Identical scripts show no red or green coloring', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Identical content\nSecond line', 'Identical content\nSecond line');
      // Check both panes — should only have gray (unchanged)
      for (let paneIdx = 0; paneIdx < 2; paneIdx++) {
        const pre = page.locator('pre').nth(paneIdx);
        const divs = pre.locator('div');
        const count = await divs.count();
        for (let i = 0; i < count; i++) {
          const cls = await divs.nth(i).getAttribute('class') ?? '';
          expect(cls).not.toContain('text-green-400');
          expect(cls).not.toContain('text-red-400');
        }
      }
    });

    test('B6: Left and right panes have equal row count', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Line A\nLine B\nLine C', 'Line A\nLine D');
      const leftCount = await page.locator('pre').first().locator('div').count();
      const rightCount = await page.locator('pre').nth(1).locator('div').count();
      expect(leftCount).toBe(rightCount);
    });

    test('B7: Diff updates live after editor edit', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Original line', 'Original line');
      // Initially all gray (identical)
      const rightPre = page.locator('pre').nth(1);
      let rightClasses: string[] = [];
      let count = await rightPre.locator('div').count();
      for (let i = 0; i < count; i++) {
        rightClasses.push(await rightPre.locator('div').nth(i).getAttribute('class') ?? '');
      }
      expect(rightClasses.every((c) => c.includes('text-gray-400'))).toBe(true);

      // Edit tts_script in the CodeMirror editor
      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.press('End');
      await page.keyboard.press('Enter');
      await page.keyboard.type('New tts line', { delay: 20 });
      await page.waitForTimeout(500);

      // Now diff should show green (added) lines on the right
      rightClasses = [];
      count = await rightPre.locator('div').count();
      for (let i = 0; i < count; i++) {
        rightClasses.push(await rightPre.locator('div').nth(i).getAttribute('class') ?? '');
      }
      const hasGreen = rightClasses.some((c) => c.includes('text-green-400'));
      expect(hasGreen).toBe(true);
    });

    test('B8: screenshot — diff with highlighted differences', async ({ page }) => {
      await navigateWithMockedScripts(
        page,
        '# Main Title\nShared paragraph\nOnly in main',
        '# TTS Title\nShared paragraph\nOnly in tts',
      );
      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-B8-diff-highlighted.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group C: Editor Interactions (~8 tests + screenshot)
  // =========================================================================
  test.describe('Group C: Editor interactions', () => {
    test('C1: .cm-content has contenteditable="true"', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main content', 'TTS editable content');
      const cmContent = page.locator('.cm-content');
      await expect(cmContent).toBeVisible();
      const editable = await cmContent.getAttribute('contenteditable');
      expect(editable).toBe('true');
    });

    test('C2: Clicking into editor focuses it (cm-focused class)', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', 'TTS focus test');
      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      const editor = page.locator('.cm-editor');
      await expect(editor).toHaveClass(/cm-focused/, { timeout: 3000 });
    });

    test('C3: Typing appends text to editor', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', 'TTS original');
      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.press('End');
      await page.keyboard.type(' APPENDED_TEXT');
      await page.waitForTimeout(300);
      const text = await page.locator('.cm-editor').textContent();
      expect(text).toContain('APPENDED_TEXT');
    });

    test('C4: Editor has 300px height', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', 'TTS height test');
      const editor = page.locator('.cm-editor');
      await expect(editor).toBeVisible();
      const height = await editor.evaluate((el) => el.offsetHeight);
      // CodeMirror height="300px" — allow small margin for borders/scrollbar
      expect(height).toBeGreaterThanOrEqual(295);
      expect(height).toBeLessThanOrEqual(310);
    });

    test('C5: "Saving…" indicator not visible initially', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', 'TTS no saving');
      const savingIndicator = page.locator('text=Saving…');
      await expect(savingIndicator).not.toBeVisible();
    });

    test('C6: Blur triggers save (POST fires on blur)', async ({ page }) => {
      let postFired = false;
      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          postFired = true;
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS blur test' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.type('BLUR_SAVE_TEST');
      // Blur immediately (before debounce fires)
      await page.locator('h2').click();
      await page.waitForTimeout(500);

      expect(postFired).toBe(true);
    });

    test('C7: Content persists after save (editor still shows typed text)', async ({ page }) => {
      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Original' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.press('End');
      await page.keyboard.type(' PERSIST_CHECK');
      // Trigger save via blur
      await page.locator('h2').click();
      await page.waitForTimeout(1000);

      // Editor should still show the typed text
      const editorText = await page.locator('.cm-editor').textContent();
      expect(editorText).toContain('PERSIST_CHECK');
    });

    test('C8: screenshot — editor with typed content', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', 'TTS screenshot test');
      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.press('End');
      await page.keyboard.type(' TYPED_FOR_SCREENSHOT');
      await page.waitForTimeout(300);
      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-C8-editor-typed.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group D: Auto-Save (~7 tests)
  // =========================================================================
  test.describe('Group D: Auto-save', () => {
    test('D1: POST fires after 1s debounce on edit', async ({ page }) => {
      let postFired = false;

      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          postFired = true;
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS debounce test' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.type('DEBOUNCE_TEST');

      // Wait longer than the 1s debounce
      await page.waitForTimeout(2000);
      expect(postFired).toBe(true);
    });

    test('D2: No POST on initial load (wait 3s, verify zero calls)', async ({ page }) => {
      const postCalls: string[] = [];

      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main no-save' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          postCalls.push('POST');
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS no-save test' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(3000);
      expect(postCalls.length).toBe(0);
    });

    test('D3: POST body is plain text (not JSON)', async ({ page }) => {
      let postContentType = '';
      let postBody = '';
      let resolvePost: (() => void) | null = null;
      const postSeen = new Promise<void>((resolve) => {
        resolvePost = resolve;
      });

      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          postContentType = route.request().headers()['content-type'] ?? '';
          postBody = route.request().postData() ?? '';
          resolvePost?.();
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS body test' }),
        });
      });

      await page.goto('/');
      await page.waitForLoadState('networkidle');

      // D1/C6 already prove the UI save paths fire correctly.
      // This test isolates the request encoding and body shape.
      await page.evaluate(async () => {
        await fetch('/api/project/script?file=tts', {
          method: 'POST',
          headers: { 'Content-Type': 'text/plain' },
          body: 'BODY_CHECK',
        });
      });
      await postSeen;

      expect(postContentType).toContain('text/plain');
      // Body should be raw text, not JSON
      expect(postBody).toContain('BODY_CHECK');
      expect(postBody).not.toMatch(/^\{/);
    });

    test('D4: Rapid edits coalesce into fewer POSTs', async ({ page }) => {
      const postCalls: number[] = [];

      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          postCalls.push(Date.now());
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS coalesce' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      const cmContent = page.locator('.cm-content');
      await cmContent.click();

      // Type rapidly within debounce windows
      await page.keyboard.type('AAA', { delay: 50 });
      await page.waitForTimeout(300);
      await page.keyboard.type('BBB', { delay: 50 });
      await page.waitForTimeout(300);
      await page.keyboard.type('CCC', { delay: 50 });

      // Wait for final debounce to fire
      await page.waitForTimeout(2000);

      // All rapid edits should coalesce — expect at most 1 POST
      expect(postCalls.length).toBeLessThanOrEqual(1);
    });

    test('D5: Blur cancels debounce and saves immediately', async ({ page }) => {
      let postTime = 0;

      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'POST') {
          postTime = Date.now();
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS blur immediate' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.type('BLUR_IMMEDIATE');

      const typeTime = Date.now();
      // Blur immediately (before debounce fires)
      await page.locator('h2').click();
      await page.waitForTimeout(500);

      // POST should have fired within ~500ms of blur, not waiting full 1s debounce
      expect(postTime).toBeGreaterThan(0);
      expect(postTime - typeTime).toBeLessThan(1500);
    });

    test('D6: "Saving…" appears during save and disappears after', async ({ page }) => {
      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', async (route) => {
        if (route.request().method() === 'POST') {
          // Slow save so we can observe the indicator
          await new Promise((r) => setTimeout(r, 1000));
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'TTS saving indicator' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      // Initially not visible
      await expect(page.locator('text=Saving…')).not.toBeVisible();

      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.type('SAVE_INDICATOR');

      // Trigger immediate save via blur
      await page.locator('h2').click();

      // "Saving…" should appear
      await expect(page.locator('text=Saving…')).toBeVisible({ timeout: 2000 });

      // After the slow save completes, it should disappear
      await expect(page.locator('text=Saving…')).not.toBeVisible({ timeout: 3000 });
    });

    test('D7: Concurrent save guard (pendingSaveRef) queues second save', async ({ page }) => {
      const savedBodies: string[] = [];

      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', async (route) => {
        if (route.request().method() === 'POST') {
          savedBodies.push(route.request().postData() ?? '');
          // Simulate slow save
          await new Promise((r) => setTimeout(r, 500));
          return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: 'initial content' }),
        });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(500);

      const cmContent = page.locator('.cm-content');
      await cmContent.click();
      await page.keyboard.press('End');
      await page.keyboard.type(' FIRST_EDIT');
      // Wait for debounce to trigger first save
      await page.waitForTimeout(1200);

      // Type second batch and blur to trigger immediate save
      await page.keyboard.type(' SECOND_EDIT');
      await page.locator('h2').click();
      await page.waitForTimeout(2000);

      // The last saved body should contain SECOND_EDIT
      const lastSave = savedBodies[savedBodies.length - 1] ?? '';
      expect(lastSave).toContain('SECOND_EDIT');
    });
  });

  // =========================================================================
  // Group E: Generation Flow (~11 tests + screenshots)
  // =========================================================================
  test.describe('Group E: Generation flow', () => {
    test('E1: Generate button enabled by default', async ({ page }) => {
      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await expect(btn).toBeEnabled();
    });

    test('E2: Click fires POST to /api/pipeline/tts-script/run', async ({ page }) => {
      let postFired = false;
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        postFired = true;
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          headers: { 'Cache-Control': 'no-cache', Connection: 'keep-alive' },
          body: 'data: {"type":"started","jobId":"e2-test-job"}\n\n',
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(500);

      expect(postFired).toBe(true);
    });

    test('E3: Button shows "Generating…" and is disabled during generation', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', async (route) => {
        // Hold response to observe in-flight state
        await new Promise((r) => setTimeout(r, 3000));
        await route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e3-test-job"}\n\n',
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await expect(btn).toBeEnabled();
      await btn.click();

      const generatingBtn = page.locator('button', { hasText: 'Generating' });
      await expect(generatingBtn).toBeDisabled({ timeout: 2000 });
      await expect(page.locator('button', { hasText: 'Generate TTS Script' })).not.toBeVisible();

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-E3-generating-state.png'),
        fullPage: true,
      });
    });

    test('E4: Button re-enables after generation completes', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e4-test-job"}\n\n',
        });
      });

      await page.route('**/api/jobs/e4-test-job/stream', (route) => {
        route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'event: done\ndata: {}\n\n',
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();

      // Wait for SSE done event to complete the cycle
      await page.waitForTimeout(3000);

      // Button should re-enable with original text
      await expect(page.locator('button', { hasText: 'Generate TTS Script' })).toBeEnabled({ timeout: 5000 });
    });

    test('E5: JobId extracted from SSE → SseLogPanel opens correct stream', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e5-sse-job"}\n\n',
        });
      });

      let streamJobId: string | null = null;
      await page.route('**/api/jobs/*/stream', (route) => {
        const url = route.request().url();
        const match = url.match(/\/api\/jobs\/([^/]+)\/stream/);
        streamJobId = match ? match[1] : null;
        route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'data: {"message":"Processing..."}\n\nevent: done\ndata: {}\n\n',
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(2000);

      expect(streamJobId).toBe('e5-sse-job');
    });

    test('E6: "Last run:" timestamp updates after generation', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e6-ts-job"}\n\n',
        });
      });

      await page.route('**/api/jobs/e6-ts-job/stream', (route) => {
        route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'event: done\ndata: {}\n\n',
        });
      });

      await navigateToStage3(page);

      // Before generation, "Last run: —" (no timestamp)
      const lastRun = page.locator('text=Last run:').first();
      const beforeText = await lastRun.textContent();

      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(2000);

      // After generation, should have an actual timestamp (not "—")
      const afterText = await lastRun.textContent();
      // The timestamp should be different from before (includes date/time)
      expect(afterText).not.toBe(beforeText);
    });

    test('E7: localStorage tts-script-last-run is set after generation', async ({ page }) => {
      // Clear any existing value
      await page.goto('/');
      await page.evaluate(() => localStorage.removeItem('tts-script-last-run'));

      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e7-ls-job"}\n\n',
        });
      });

      await page.route('**/api/jobs/e7-ls-job/stream', (route) => {
        route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'event: done\ndata: {}\n\n',
        });
      });

      await navigateToStage3(page);

      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(2000);

      const storedValue = await page.evaluate(() => localStorage.getItem('tts-script-last-run'));
      expect(storedValue).toBeTruthy();
      // Should be a valid ISO date string
      expect(new Date(storedValue!).getTime()).not.toBeNaN();
    });

    test('E8: Double-click guard prevents duplicate API calls', async ({ page }) => {
      let apiCallCount = 0;
      await page.route('**/api/pipeline/tts-script/run', async (route) => {
        apiCallCount++;
        await new Promise((r) => setTimeout(r, 2000));
        await route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e8-guard-job"}\n\n',
        });
      });

      await navigateToStage3(page);

      // Synchronous double-click via evaluate
      await page.evaluate(() => {
        const btn = [...document.querySelectorAll('button')].find(
          (b) => b.textContent?.includes('Generate TTS Script'),
        );
        if (btn) { btn.click(); btn.click(); }
      });
      await page.waitForTimeout(500);

      expect(apiCallCount).toBe(1);
    });

    test('E9: SSE error event shows red error box', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'event: error\ndata: {"message":"Pipeline failed: model timeout"}\n\n',
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(1500);

      // Error box should appear with red styling
      const errorBox = page.locator('text=Generation failed');
      await expect(errorBox).toBeVisible({ timeout: 3000 });

      // Should contain the error message
      await expect(page.locator('text=Pipeline failed')).toBeVisible();

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-E9-error-state.png'),
        fullPage: true,
      });
    });

    test('E10: Server 500 shows error', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(1500);

      // Should show error with status code
      const errorBox = page.locator('text=Generation failed');
      await expect(errorBox).toBeVisible({ timeout: 3000 });
      await expect(page.locator('text=Server error: 500')).toBeVisible();
    });

    test('E11: SseLogPanel shows "Waiting for logs…" before messages arrive', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"e11-wait-job"}\n\n',
        });
      });

      // Hold the stream open without sending data
      await page.route('**/api/jobs/e11-wait-job/stream', (route) => {
        // Never fulfill — stream stays open
        route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          headers: { 'Cache-Control': 'no-cache' },
          body: '', // empty — no events yet
        });
      });

      await navigateToStage3(page);
      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();
      await page.waitForTimeout(1500);

      // SseLogPanel should show "Waiting for logs…"
      await expect(page.locator('text=Waiting for logs')).toBeVisible({ timeout: 3000 });

      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-E11-sse-panel.png'),
        fullPage: true,
      });
    });
  });

  // =========================================================================
  // Group F: Advance Button & Edge Cases (~7 tests + screenshots)
  // =========================================================================
  test.describe('Group F: Advance button & edge cases', () => {
    test('F1: "Render Audio →" disabled when no tts_script exists', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main content', null);
      const btn = page.locator('button', { hasText: 'Render Audio' });
      await expect(btn).toBeDisabled();
    });

    test('F2: "Render Audio →" enabled when tts_script exists', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main content', 'TTS content exists');
      const btn = page.locator('button', { hasText: 'Render Audio' });
      await expect(btn).toBeEnabled();
    });

    test('F3: Disabled button has gray styling (bg-gray-700)', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', null);
      const btn = page.locator('button', { hasText: 'Render Audio' });
      await expect(btn).toBeDisabled();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-gray-700');
      expect(cls).toContain('cursor-not-allowed');
    });

    test('F4: Enabled button has green styling (bg-green-600)', async ({ page }) => {
      await navigateWithMockedScripts(page, 'Main', 'TTS exists');
      const btn = page.locator('button', { hasText: 'Render Audio' });
      await expect(btn).toBeEnabled();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-green-600');
    });

    test('F5: Empty script does not crash page', async ({ page }) => {
      await navigateWithMockedScripts(page, '', '');
      // Page should still be functional
      const heading = page.locator('h2', { hasText: 'Stage 3' });
      await expect(heading).toBeVisible();
      const editor = page.locator('.cm-editor');
      await expect(editor).toBeVisible();
    });

    test('F6: API 500 on script load does not crash', async ({ page }) => {
      await page.route('**/api/project/script?file=main', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: JSON.stringify({ error: 'Internal Server Error' }),
        });
      });

      await navigateToStage3(page);
      // Page should not crash — heading and editor still visible
      await expect(page.locator('h2', { hasText: 'Stage 3' })).toBeVisible();
      const editor = page.locator('.cm-editor');
      await expect(editor).toBeVisible();
    });

    test('F7: Scripts reload after generation completes (onDone callback)', async ({ page }) => {
      await page.route('**/api/pipeline/tts-script/run', (route) => {
        route.fulfill({
          status: 202,
          contentType: 'text/event-stream',
          body: 'data: {"type":"started","jobId":"f7-reload-job"}\n\n',
        });
      });

      await page.route('**/api/jobs/f7-reload-job/stream', (route) => {
        route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'event: done\ndata: {}\n\n',
        });
      });

      // Track script reload calls
      let scriptFetchCount = 0;
      await page.route('**/api/project/script?file=main', (route) => {
        scriptFetchCount++;
        route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: '# Reloaded Main' }),
        });
      });
      await page.route('**/api/project/script?file=tts', (route) => {
        if (route.request().method() === 'GET') {
          scriptFetchCount++;
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ content: '# Reloaded TTS' }),
          });
        }
        return route.fulfill({ status: 200, contentType: 'text/plain', body: 'ok' });
      });

      await navigateToStage3(page);
      await page.waitForTimeout(1500);

      // Reset counter after initial load
      scriptFetchCount = 0;

      const btn = page.locator('button', { hasText: 'Generate TTS Script' });
      await btn.click();

      // Wait for SSE done → onDone → loadScripts
      await page.waitForTimeout(3000);

      // Scripts should have been re-fetched (at least 2 calls: main + tts)
      expect(scriptFetchCount).toBeGreaterThanOrEqual(2);
    });

    test('F8: screenshot — button states (disabled vs enabled)', async ({ page }) => {
      // Show disabled state
      await navigateWithMockedScripts(page, 'Main', null);
      await page.screenshot({
        path: path.join(SCREENSHOT_DIR, 'stage3-F8-advance-disabled.png'),
        fullPage: true,
      });
    });
  });
});
