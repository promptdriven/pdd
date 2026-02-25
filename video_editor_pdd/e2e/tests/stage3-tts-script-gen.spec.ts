import { test, expect } from '@playwright/test';

test.describe('Stage 3: TTS Script Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on TTS Script stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'TTS Script' }).first().click();
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
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-tts-gen-job' }),
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
});
