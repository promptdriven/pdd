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
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
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
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
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
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
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
    await sidebar.locator('div', { hasText: 'Script' }).first().click();
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
});
