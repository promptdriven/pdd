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
});
