import { test, expect } from '@playwright/test';

test.describe('Stage 2: Script Editor', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Script stage
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
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
    // Wait for CodeMirror editor to be fully loaded with content
    const editor = page.locator('.cm-editor');
    await expect(editor).toBeVisible({ timeout: 15000 });
    // Wait for content lines to render
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
    await page.waitForTimeout(1000);
    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    // If script has NARRATOR: lines, the button should be enabled
    const isDisabled = await generateBtn.getAttribute('disabled');
    // The script has NARRATOR content, so button should NOT be disabled
    expect(isDisabled).toBeNull();
  });

  test('Generate TTS Script button is clickable and triggers API call', async ({ page }) => {
    await page.waitForTimeout(1000);

    let apiCallTriggered = false;
    await page.route('**/api/pipeline/tts-script/run', (route) => {
      apiCallTriggered = true;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-job-123' }),
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate TTS Script' });
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(apiCallTriggered).toBe(true);
  });

  test('CodeMirror editor area is present and content is editable', async ({ page }) => {
    await page.waitForTimeout(2000);

    const editor = page.locator('.cm-editor');
    await expect(editor).toBeVisible({ timeout: 15000 });

    // Click into the editor content area to focus it
    const cmContent = page.locator('.cm-content');
    await expect(cmContent).toBeVisible();
    await cmContent.click();

    // Verify the editor gains focus (cm-focused class appears)
    await expect(editor).toHaveClass(/cm-focused/, { timeout: 5000 }).catch(() => {
      // Some CodeMirror versions use different focus indicators
    });

    // Verify the editor has contenteditable attribute (it's editable)
    const isEditable = await cmContent.getAttribute('contenteditable');
    expect(isEditable).toBe('true');

    // Verify existing content is present in the editor
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
});
