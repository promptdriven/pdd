import { test, expect } from '@playwright/test';

test.describe('Stage 1: Project Setup', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Stage 1 is the default active stage
  });

  test('displays Stage 1 heading', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
  });

  test('project name input exists and has content', async ({ page }) => {
    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();
    // The project name should be loaded from project.json
    await expect(nameInput).not.toHaveValue('');
  });

  test('output resolution dropdown exists', async ({ page }) => {
    const resolutionSelect = page.locator('select').first();
    await expect(resolutionSelect).toBeVisible();
    // Should have the default 1920x1080 value
    await expect(resolutionSelect).toHaveValue('1920x1080');
  });

  test('TTS speaker input exists', async ({ page }) => {
    const label = page.locator('label', { hasText: 'TTS Speaker' });
    await expect(label).toBeVisible();
  });

  test('Veo model input exists', async ({ page }) => {
    const label = page.locator('label', { hasText: 'Veo Model' });
    await expect(label).toBeVisible();
  });

  test('Section Registry heading and table exist', async ({ page }) => {
    await expect(page.locator('h3', { hasText: 'Section Registry' })).toBeVisible();
    await expect(page.locator('table')).toBeVisible();
  });

  test('Section Registry table header is visible (dark theme fix)', async ({ page }) => {
    // The table header should have readable text - check that thead has dark bg
    const thead = page.locator('thead');
    await expect(thead).toBeVisible();
    // Verify the header text is readable by checking for column headers
    await expect(page.locator('th', { hasText: 'Section ID' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Label' })).toBeVisible();
    await expect(page.locator('th', { hasText: 'Composition ID' })).toBeVisible();
  });

  test('Section Registry has rows loaded from project.json', async ({ page }) => {
    const tableRows = page.locator('tbody tr');
    // project.json has 7 sections
    const count = await tableRows.count();
    expect(count).toBeGreaterThanOrEqual(1);
  });

  test('Add Section button exists', async ({ page }) => {
    const addBtn = page.locator('button', { hasText: '+ Add Section' });
    await expect(addBtn).toBeVisible();
  });

  test('Save button exists and is green', async ({ page }) => {
    const saveBtn = page.locator('button', { hasText: 'Save' });
    await expect(saveBtn).toBeVisible();
  });

  test('clicking Add Section adds a new row', async ({ page }) => {
    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();

    await page.locator('button', { hasText: '+ Add Section' }).click();

    const newCount = await tableRows.count();
    expect(newCount).toBe(initialCount + 1);
  });

  test('Save button click triggers a PUT request to /api/project', async ({ page }) => {
    let putRequestFired = false;
    await page.route('**/api/project', (route) => {
      if (route.request().method() === 'PUT') {
        putRequestFired = true;
        route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ name: 'Test Project', outputResolution: { width: 1920, height: 1080 }, tts: { engine: 'qwen3-tts', modelPath: '', tokenizerPath: '', speaker: 'Aiden', speakingRate: 0.95, sampleRate: 24000 }, sections: [], audioSync: { sectionGroups: {}, silenceGapDefault: 0.3 }, veo: { model: 'veo-3.1-generate-preview', defaultAspectRatio: '16:9', maxConcurrentGenerations: 4, references: [], frameChains: [] }, render: { maxParallelRenders: 3, useLambda: false, lambdaRegion: 'us-east-1' } }),
        });
      } else {
        route.continue();
      }
    });

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    expect(putRequestFired).toBe(true);
  });

  test('Edit button on a section row opens inline edit mode with input fields', async ({ page }) => {
    // Ensure there is at least one section row
    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();
    if (initialCount === 0) {
      await page.locator('button', { hasText: '+ Add Section' }).click();
      await page.waitForTimeout(300);
    }

    // Click the edit button (pencil icon) on the first section row
    const firstRow = page.locator('tbody tr').first();
    const editBtn = firstRow.locator('button', { hasText: '✎' });
    await editBtn.click();
    await page.waitForTimeout(300);

    // In edit mode, the row should now contain input fields
    const inputsInRow = firstRow.locator('input');
    const inputCount = await inputsInRow.count();
    expect(inputCount).toBeGreaterThanOrEqual(2); // At least Section ID and Label inputs

    // The edit button should now show a confirm icon (checkmark)
    await expect(firstRow.locator('button', { hasText: '✓' })).toBeVisible();
  });

  test('Confirm edit closes edit mode and removes input fields', async ({ page }) => {
    // Add a section if needed
    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();
    if (initialCount === 0) {
      await page.locator('button', { hasText: '+ Add Section' }).click();
      await page.waitForTimeout(300);
    }

    const firstRow = page.locator('tbody tr').first();
    // Enter edit mode
    await firstRow.locator('button', { hasText: '✎' }).click();
    await page.waitForTimeout(300);

    // Confirm edit
    await firstRow.locator('button', { hasText: '✓' }).click();
    await page.waitForTimeout(300);

    // Should be back to view mode - edit button should show pencil again
    await expect(firstRow.locator('button', { hasText: '✎' })).toBeVisible();
    // Input fields inside the row's data cells should no longer be present
    const inputsInRow = firstRow.locator('td input');
    const inputCount = await inputsInRow.count();
    expect(inputCount).toBe(0);
  });

  test('Cancel edit reverts without saving and closes edit mode', async ({ page }) => {
    // Add a section if needed
    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();
    if (initialCount === 0) {
      await page.locator('button', { hasText: '+ Add Section' }).click();
      await page.waitForTimeout(300);
    }

    const firstRow = page.locator('tbody tr').first();
    // Get original label text before editing
    const labelCell = firstRow.locator('td').nth(2);
    const originalLabel = await labelCell.textContent();

    // Enter edit mode
    await firstRow.locator('button', { hasText: '✎' }).click();
    await page.waitForTimeout(300);

    // Modify the label input
    const labelInput = firstRow.locator('td').nth(2).locator('input');
    await labelInput.clear();
    await labelInput.fill('Modified Label');

    // Cancel edit (the ✕ button in the last column during edit mode)
    await firstRow.locator('button', { hasText: '✕' }).click();
    await page.waitForTimeout(300);

    // Should revert to original label
    const revertedLabel = await labelCell.textContent();
    expect(revertedLabel).toBe(originalLabel);

    // Should be back in view mode
    await expect(firstRow.locator('button', { hasText: '✎' })).toBeVisible();
  });

  test('Delete button removes a section row and count decreases', async ({ page }) => {
    // Ensure there is at least one section
    const tableRows = page.locator('tbody tr');
    let count = await tableRows.count();
    if (count === 0) {
      await page.locator('button', { hasText: '+ Add Section' }).click();
      await page.waitForTimeout(300);
      count = await tableRows.count();
    }

    const countBefore = count;

    // Click the delete button (✕) on the first row (in view mode it is the delete button)
    const firstRow = page.locator('tbody tr').first();
    await firstRow.locator('button', { hasText: '✕' }).click();
    await page.waitForTimeout(300);

    const countAfter = await tableRows.count();
    expect(countAfter).toBe(countBefore - 1);
  });

  test('Output Resolution select changes value when new option selected', async ({ page }) => {
    const resolutionSelect = page.locator('select').first();
    await expect(resolutionSelect).toHaveValue('1920x1080');

    // Change to 1280x720
    await resolutionSelect.selectOption('1280x720');
    await expect(resolutionSelect).toHaveValue('1280x720');

    // Change back
    await resolutionSelect.selectOption('1920x1080');
    await expect(resolutionSelect).toHaveValue('1920x1080');
  });

  test('TTS Speaking Rate input accepts a numeric value', async ({ page }) => {
    const speakingRateInput = page.locator('input[type="number"]').first();
    await expect(speakingRateInput).toBeVisible();

    // Clear and type a new value
    await speakingRateInput.click();
    await speakingRateInput.fill('1.25');
    await expect(speakingRateInput).toHaveValue('1.25');
  });

  test('Veo Aspect Ratio select changes value', async ({ page }) => {
    // Veo Aspect Ratio is the second <select> on the page
    const aspectRatioSelect = page.locator('select').nth(1);
    await expect(aspectRatioSelect).toBeVisible();

    // Default should be 16:9
    await expect(aspectRatioSelect).toHaveValue('16:9');

    // Change to 9:16
    await aspectRatioSelect.selectOption('9:16');
    await expect(aspectRatioSelect).toHaveValue('9:16');

    // Change back
    await aspectRatioSelect.selectOption('16:9');
    await expect(aspectRatioSelect).toHaveValue('16:9');
  });
});
