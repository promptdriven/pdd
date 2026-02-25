import { test, expect } from '@playwright/test';

// Valid mock response for PUT /api/project (matches the shape used by existing tests)
const MOCK_PROJECT_RESPONSE = {
  name: 'Test Project',
  outputResolution: { width: 1920, height: 1080 },
  tts: {
    engine: 'qwen3-tts',
    modelPath: '',
    tokenizerPath: '',
    speaker: 'Aiden',
    speakingRate: 0.95,
    sampleRate: 24000,
  },
  sections: [],
  audioSync: { sectionGroups: {}, silenceGapDefault: 0.3 },
  veo: {
    model: 'veo-3.1-generate-preview',
    defaultAspectRatio: '16:9',
    maxConcurrentGenerations: 4,
    references: [],
    frameChains: [],
  },
  render: { maxParallelRenders: 3, useLambda: false, lambdaRegion: 'us-east-1' },
};

/**
 * Helper: intercept PUT /api/project and return 200 with a valid body.
 * Also passes through any other method (GET) so the page loads normally.
 */
async function mockPutProject(page: import('@playwright/test').Page) {
  await page.route('**/api/project', (route) => {
    if (route.request().method() === 'PUT') {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(MOCK_PROJECT_RESPONSE),
      });
    }
    return route.continue();
  });
}

// ---------------------------------------------------------------------------
// TTS Speaking Rate Boundaries
// ---------------------------------------------------------------------------
test.describe('TTS Speaking Rate Boundaries', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('set speaking rate to 0 — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const speakingRate = page.locator('input[type="number"]').first();
    await expect(speakingRate).toBeVisible();

    await speakingRate.click();
    await speakingRate.fill('0');
    await expect(speakingRate).toHaveValue('0');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    // Page should not crash — heading still visible
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set speaking rate to 5 (above max) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const speakingRate = page.locator('input[type="number"]').first();
    await speakingRate.click();
    await speakingRate.fill('5');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set speaking rate to -1 (negative) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const speakingRate = page.locator('input[type="number"]').first();
    await speakingRate.click();
    await speakingRate.fill('-1');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set speaking rate to non-numeric "abc" — input rejects or stays safe', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    const speakingRate = page.locator('input[type="number"]').first();
    await expect(speakingRate).toBeVisible();

    await speakingRate.click();
    await speakingRate.fill('abc');

    // number inputs reject non-numeric text; value should be empty
    const value = await speakingRate.inputValue();
    expect(value === '' || value === 'abc').toBe(true);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// TTS Sample Rate Boundaries
// ---------------------------------------------------------------------------
test.describe('TTS Sample Rate Boundaries', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('set sample rate to 0 — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const sampleRate = page.locator('input[type="number"]').nth(1);
    await expect(sampleRate).toBeVisible();

    await sampleRate.click();
    await sampleRate.fill('0');
    await expect(sampleRate).toHaveValue('0');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set sample rate to -1 (negative) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const sampleRate = page.locator('input[type="number"]').nth(1);
    await sampleRate.click();
    await sampleRate.fill('-1');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set sample rate to very large number (999999) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const sampleRate = page.locator('input[type="number"]').nth(1);
    await sampleRate.click();
    await sampleRate.fill('999999');
    await expect(sampleRate).toHaveValue('999999');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Max Parallel Renders Boundaries
// ---------------------------------------------------------------------------
test.describe('Max Parallel Renders Boundaries', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('set to 0 (below min 1) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const maxRenders = page.locator('input[type="number"]').nth(2);
    await expect(maxRenders).toBeVisible();

    await maxRenders.click();
    await maxRenders.fill('0');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set to 100 (above max 4) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const maxRenders = page.locator('input[type="number"]').nth(2);
    await maxRenders.click();
    await maxRenders.fill('100');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('set to non-numeric "abc" — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    const maxRenders = page.locator('input[type="number"]').nth(2);
    await expect(maxRenders).toBeVisible();

    await maxRenders.click();
    await maxRenders.fill('abc');

    // number input should reject non-numeric text
    const value = await maxRenders.inputValue();
    expect(value === '' || value === 'abc').toBe(true);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Project Name Edge Cases
// ---------------------------------------------------------------------------
test.describe('Project Name Edge Cases', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('empty project name — no crash on save', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();

    await nameInput.clear();
    await expect(nameInput).toHaveValue('');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('very long project name (500 chars) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();

    const longName = 'A'.repeat(500);
    await nameInput.clear();
    await nameInput.fill(longName);

    // Verify the value was set (input may truncate, but no crash)
    const value = await nameInput.inputValue();
    expect(value.length).toBeGreaterThan(0);

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('special characters in name (XSS attempt) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();

    await nameInput.clear();
    await nameInput.fill('Test <script>alert(1)</script>');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    // Page should not crash and no script should execute
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('unicode characters in name — value preserved and no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const nameInput = page.locator('input').first();
    await expect(nameInput).toBeVisible();

    const unicodeName = '\u30C6\u30B9\u30C8\u52D5\u753B\u30D7\u30ED\u30B8\u30A7\u30AF\u30C8 \uD83C\uDFAC';
    await nameInput.clear();
    await nameInput.fill(unicodeName);
    await expect(nameInput).toHaveValue(unicodeName);

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Veo Model Edge Cases
// ---------------------------------------------------------------------------
test.describe('Veo Model Edge Cases', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('empty veo model — no crash on save', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const veoModelLabel = page.locator('label', { hasText: 'Veo Model' });
    await expect(veoModelLabel).toBeVisible();
    const veoModelDiv = veoModelLabel.locator('..');
    const veoModelInput = veoModelDiv.locator('input');
    await expect(veoModelInput).toBeVisible();

    await veoModelInput.clear();
    await expect(veoModelInput).toHaveValue('');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('special characters in model name (path traversal attempt) — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const veoModelLabel = page.locator('label', { hasText: 'Veo Model' });
    const veoModelDiv = veoModelLabel.locator('..');
    const veoModelInput = veoModelDiv.locator('input');
    await expect(veoModelInput).toBeVisible();

    await veoModelInput.clear();
    await veoModelInput.fill('model/../../../etc/passwd');

    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});

// ---------------------------------------------------------------------------
// Section Operations Edge Cases
// ---------------------------------------------------------------------------
test.describe('Section Operations Edge Cases', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  test('add section then immediately delete — row count returns to original', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();

    // Add a new section
    await page.locator('button', { hasText: '+ Add Section' }).click();
    await page.waitForTimeout(300);
    expect(await tableRows.count()).toBe(initialCount + 1);

    // Delete the last row (the newly added one)
    const lastRow = tableRows.last();
    await lastRow.locator('button', { hasText: '\u2715' }).click();
    await page.waitForTimeout(300);

    // Count should return to original
    expect(await tableRows.count()).toBe(initialCount);

    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('edit section with empty ID — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    const tableRows = page.locator('tbody tr');
    const count = await tableRows.count();
    expect(count).toBeGreaterThanOrEqual(1);

    const firstRow = tableRows.first();

    // Enter edit mode
    await firstRow.locator('button', { hasText: '\u270E' }).click();
    await page.waitForTimeout(300);

    // Clear the Section ID input (td[1] in edit mode)
    const sectionIdInput = firstRow.locator('td').nth(1).locator('input');
    await expect(sectionIdInput).toBeVisible();
    await sectionIdInput.clear();

    // Confirm the edit
    await firstRow.locator('button', { hasText: '\u2713' }).click();
    await page.waitForTimeout(300);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('edit section with special characters in ID — no crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));

    const tableRows = page.locator('tbody tr');
    expect(await tableRows.count()).toBeGreaterThanOrEqual(1);

    const firstRow = tableRows.first();

    // Enter edit mode
    await firstRow.locator('button', { hasText: '\u270E' }).click();
    await page.waitForTimeout(300);

    // Fill Section ID with special characters
    const sectionIdInput = firstRow.locator('td').nth(1).locator('input');
    await expect(sectionIdInput).toBeVisible();
    await sectionIdInput.clear();
    await sectionIdInput.fill('../test section/');

    // Confirm the edit
    await firstRow.locator('button', { hasText: '\u2713' }).click();
    await page.waitForTimeout(300);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('delete all sections then save — no crash, then re-add works', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (e) => errors.push(e.message));
    await mockPutProject(page);

    const tableRows = page.locator('tbody tr');
    const initialCount = await tableRows.count();
    expect(initialCount).toBe(7);

    // Delete all 7 sections one by one (always delete the first remaining row)
    for (let i = 0; i < initialCount; i++) {
      const firstRow = tableRows.first();
      await firstRow.locator('button', { hasText: '\u2715' }).click();
      await page.waitForTimeout(200);
    }

    // All rows should be gone
    expect(await tableRows.count()).toBe(0);

    // Save with zero sections
    const saveBtn = page.locator('button', { hasText: 'Save' });
    await saveBtn.click();
    await page.waitForTimeout(500);

    // Page should not crash
    await expect(page.locator('h2', { hasText: 'Stage 1: Project Setup' })).toBeVisible();
    await expect(saveBtn).toBeVisible();

    // Re-add a section to verify + Add still works
    await page.locator('button', { hasText: '+ Add Section' }).click();
    await page.waitForTimeout(300);
    expect(await tableRows.count()).toBe(1);

    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
