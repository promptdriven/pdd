import { test, expect } from '@playwright/test';

test.describe('Stage 2: Script Editor', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Script stage
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
    // Wait for stage to load
    await page.waitForTimeout(500);
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
    // Wait for content to load
    await page.waitForTimeout(1000);
    // The editor should have content (from the script API)
    const editor = page.locator('.cm-editor');
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
});
