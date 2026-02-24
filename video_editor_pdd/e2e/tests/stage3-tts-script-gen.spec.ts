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

    // The content should contain actual markdown (the script starts with # heading)
    // Even if tts_script is empty, main_script should show the parsed markdown
    if (diffText && diffText.trim().length > 0) {
      expect(diffText).toContain('Prompt-Driven Development');
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
});
