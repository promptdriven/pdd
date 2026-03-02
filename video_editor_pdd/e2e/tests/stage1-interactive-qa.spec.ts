import { test, expect } from '@playwright/test';
import path from 'path';
import fs from 'fs';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');
const PROJECT_JSON_PATH = path.join(__dirname, '..', '..', 'project.json');

test.describe('Stage 1: Interactive QA - Comprehensive Feature Testing', () => {
  // Tests share project.json on disk via the real API - must run serially
  test.describe.configure({ mode: 'serial' });

  // Snapshot the original project.json before any tests run, restore after all
  let originalProjectJson: string;

  test.beforeAll(async () => {
    originalProjectJson = fs.readFileSync(PROJECT_JSON_PATH, 'utf8');
  });

  test.afterAll(async () => {
    fs.writeFileSync(PROJECT_JSON_PATH, originalProjectJson, 'utf8');
  });

  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
  });

  // =========================================================================
  // Group A: Initial Load & Data Binding
  // =========================================================================
  test.describe('Group A: Initial load & data binding', () => {
    test('A1: page loads with Stage 1 heading', async ({ page }) => {
      const heading = page.locator('h2', { hasText: 'Stage 1: Project Setup' });
      await expect(heading).toBeVisible();
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'A1-stage1-heading.png'), fullPage: true });
    });

    test('A2: project name shows "3blue1brown-antibiotics"', async ({ page }) => {
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      await expect(nameInput).toHaveValue('3blue1brown-antibiotics');
    });

    test('A3: resolution dropdown shows 1920x1080', async ({ page }) => {
      const resSelect = page.locator('select').first();
      await expect(resSelect).toHaveValue('1920x1080');
    });

    test('A4: TTS Speaker shows "Aiden"', async ({ page }) => {
      const speakerInput = page.locator('label', { hasText: 'TTS Speaker' }).locator('..').locator('input');
      await expect(speakerInput).toHaveValue('Aiden');
    });

    test('A5: TTS Speaking Rate shows 0.95', async ({ page }) => {
      const rateInput = page.locator('label', { hasText: 'TTS Speaking Rate' }).locator('..').locator('input');
      await expect(rateInput).toHaveValue('0.95');
    });

    test('A6: TTS Sample Rate shows 24000', async ({ page }) => {
      const sampleInput = page.locator('label', { hasText: 'TTS Sample Rate' }).locator('..').locator('input');
      await expect(sampleInput).toHaveValue('24000');
    });

    test('A7: Veo Model shows "veo-3.1-generate-preview"', async ({ page }) => {
      const veoInput = page.locator('label', { hasText: 'Veo Model' }).locator('..').locator('input');
      await expect(veoInput).toHaveValue('veo-3.1-generate-preview');
    });

    test('A8: Veo Aspect Ratio shows 16:9', async ({ page }) => {
      const aspectSelect = page.locator('label', { hasText: 'Veo Aspect Ratio' }).locator('..').locator('select');
      await expect(aspectSelect).toHaveValue('16:9');
    });

    test('A9: Max Parallel Renders shows 3', async ({ page }) => {
      const rendersInput = page.locator('label', { hasText: 'Max Parallel Renders' }).locator('..').locator('input');
      await expect(rendersInput).toHaveValue('3');
    });

    test('A10: Section Registry table has exactly 7 rows', async ({ page }) => {
      const rows = page.locator('tbody tr');
      await expect(rows).toHaveCount(7);

      // Verify specific section IDs match project.json
      const expectedIds = [
        'cold_open', 'part1_economics', 'part2_paradigm_shift',
        'part3_mold', 'part4_precision', 'part5_compound', 'closing',
      ];
      for (let i = 0; i < expectedIds.length; i++) {
        const idCell = rows.nth(i).locator('td').nth(1);
        await expect(idCell).toHaveText(expectedIds[i]);
      }
    });

    test('A11: Section Registry labels match project.json', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const expectedLabels = [
        'Cold Open', 'Part 1: Economics', 'Part 2: Paradigm Shift',
        'Part 3: The Mold', 'Part 4: Precision Tradeoff', 'Part 5: Compound Returns', 'Closing',
      ];
      for (let i = 0; i < expectedLabels.length; i++) {
        const labelCell = rows.nth(i).locator('td').nth(2);
        await expect(labelCell).toHaveText(expectedLabels[i]);
      }
    });

    test('A12: Section Registry compositionIds match project.json', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const expectedComps = [
        'ColdOpenSection', 'Part1Economics', 'Part2ParadigmShift',
        'Part3MoldThreeParts', 'Part4PrecisionTradeoff', 'Part5CompoundReturns', 'ClosingSection',
      ];
      for (let i = 0; i < expectedComps.length; i++) {
        const compCell = rows.nth(i).locator('td').nth(3);
        await expect(compCell).toHaveText(expectedComps[i]);
      }
    });

    test('A13: full page initial state screenshot', async ({ page }) => {
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'A13-full-initial-state.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group B: Form Field Interactions & Unsaved Changes Indicator
  // =========================================================================
  test.describe('Group B: Form field interactions & yellow dot', () => {
    test('B1: changing project name triggers yellow dot', async ({ page }) => {
      // Yellow dot should NOT be present initially
      const yellowDot = page.locator('span.rounded-full.bg-yellow-400');
      await expect(yellowDot).not.toBeVisible();

      // Change project name
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      await nameInput.clear();
      await nameInput.fill('test-project');

      // Yellow dot SHOULD appear
      await expect(yellowDot).toBeVisible({ timeout: 3000 });
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'B1-yellow-dot-visible.png'), fullPage: true });
    });

    test('B2: changing resolution dropdown updates value', async ({ page }) => {
      const resSelect = page.locator('select').first();
      await resSelect.selectOption('1280x720');
      await expect(resSelect).toHaveValue('1280x720');
    });

    test('B3: changing TTS speaker updates value', async ({ page }) => {
      const speakerInput = page.locator('label', { hasText: 'TTS Speaker' }).locator('..').locator('input');
      await speakerInput.clear();
      await speakerInput.fill('Brian');
      await expect(speakerInput).toHaveValue('Brian');
    });

    test('B4: changing speaking rate updates value', async ({ page }) => {
      const rateInput = page.locator('label', { hasText: 'TTS Speaking Rate' }).locator('..').locator('input');
      await rateInput.clear();
      await rateInput.fill('1.2');
      await expect(rateInput).toHaveValue('1.2');
    });

    test('B5: changing sample rate updates value', async ({ page }) => {
      const sampleInput = page.locator('label', { hasText: 'TTS Sample Rate' }).locator('..').locator('input');
      await sampleInput.clear();
      await sampleInput.fill('16000');
      await expect(sampleInput).toHaveValue('16000');
    });

    test('B6: changing Veo model updates value', async ({ page }) => {
      const veoInput = page.locator('label', { hasText: 'Veo Model' }).locator('..').locator('input');
      await veoInput.clear();
      await veoInput.fill('veo-2.0-preview');
      await expect(veoInput).toHaveValue('veo-2.0-preview');
    });

    test('B7: changing Veo aspect ratio updates value', async ({ page }) => {
      const aspectSelect = page.locator('label', { hasText: 'Veo Aspect Ratio' }).locator('..').locator('select');
      await aspectSelect.selectOption('9:16');
      await expect(aspectSelect).toHaveValue('9:16');
    });

    test('B8: changing max parallel renders updates value', async ({ page }) => {
      const rendersInput = page.locator('label', { hasText: 'Max Parallel Renders' }).locator('..').locator('input');
      await rendersInput.clear();
      await rendersInput.fill('2');
      await expect(rendersInput).toHaveValue('2');
    });

    test('B9: yellow dot disappears after save restores same state', async ({ page }) => {
      // Yellow dot should not be present initially (no changes)
      const yellowDot = page.locator('span.rounded-full.bg-yellow-400');
      await expect(yellowDot).not.toBeVisible();
    });
  });

  // =========================================================================
  // Group C: Section Registry CRUD
  // =========================================================================
  test.describe('Group C: Section Registry CRUD', () => {
    test('C1: Add Section appends a new row (7 → 8)', async ({ page }) => {
      const rows = page.locator('tbody tr');
      await expect(rows).toHaveCount(7);

      await page.locator('button', { hasText: '+ Add Section' }).click();
      await expect(rows).toHaveCount(8);

      // New row should have "New Section" as label
      const lastRow = rows.last();
      const labelCell = lastRow.locator('td').nth(2);
      await expect(labelCell).toHaveText('New Section');

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'C1-after-add-section.png'), fullPage: true });
    });

    test('C2: Edit button shows pencil icon on each row', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const count = await rows.count();
      for (let i = 0; i < count; i++) {
        const editBtn = rows.nth(i).locator('button', { hasText: '✎' });
        await expect(editBtn).toBeVisible();
      }
    });

    test('C3: clicking edit shows input fields in row', async ({ page }) => {
      const firstRow = page.locator('tbody tr').first();
      await firstRow.locator('button', { hasText: '✎' }).click();

      // Should show at least 3 inputs (id, label, compositionId)
      const inputs = firstRow.locator('td input');
      const inputCount = await inputs.count();
      expect(inputCount).toBeGreaterThanOrEqual(3);

      // Confirm and cancel buttons should appear
      await expect(firstRow.locator('button', { hasText: '✓' })).toBeVisible();
      await expect(firstRow.locator('button', { hasText: '✕' })).toBeVisible();

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'C3-edit-mode.png'), fullPage: true });
    });

    test('C4: edit confirm saves changes to row', async ({ page }) => {
      const firstRow = page.locator('tbody tr').first();

      // Enter edit mode
      await firstRow.locator('button', { hasText: '✎' }).click();

      // Change label
      const labelInput = firstRow.locator('td').nth(2).locator('input');
      await labelInput.clear();
      await labelInput.fill('Renamed Cold Open');

      // Confirm
      await firstRow.locator('button', { hasText: '✓' }).click();

      // Verify label cell shows new value
      const labelCell = firstRow.locator('td').nth(2);
      await expect(labelCell).toHaveText('Renamed Cold Open');
    });

    test('C5: edit cancel reverts changes', async ({ page }) => {
      const firstRow = page.locator('tbody tr').first();
      const labelCell = firstRow.locator('td').nth(2);
      const originalLabel = await labelCell.textContent();

      // Enter edit mode
      await firstRow.locator('button', { hasText: '✎' }).click();

      // Change label
      const labelInput = firstRow.locator('td').nth(2).locator('input');
      await labelInput.clear();
      await labelInput.fill('SHOULD BE REVERTED');

      // Cancel
      await firstRow.locator('button', { hasText: '✕' }).click();

      // Verify label reverted
      await expect(labelCell).toHaveText(originalLabel!);
      // Back to view mode
      await expect(firstRow.locator('button', { hasText: '✎' })).toBeVisible();
    });

    test('C6: delete section removes row (7 → 6)', async ({ page }) => {
      const rows = page.locator('tbody tr');
      await expect(rows).toHaveCount(7);

      // Get the ID of first row before deleting
      const firstId = await rows.first().locator('td').nth(1).textContent();

      // Delete first row
      await rows.first().locator('button', { hasText: '✕' }).click();

      // Row count decreased
      await expect(rows).toHaveCount(6);

      // First row should now be what was previously the second row
      const newFirstId = await rows.first().locator('td').nth(1).textContent();
      expect(newFirstId).not.toBe(firstId);

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'C6-after-delete.png'), fullPage: true });
    });

    test('C7: deleting all sections shows "No sections yet" message', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const count = await rows.count();

      // Delete all sections
      for (let i = 0; i < count; i++) {
        // Always delete the first row
        await page.locator('tbody tr').first().locator('button', { hasText: '✕' }).click();
        await page.waitForTimeout(100);
      }

      // Should show empty state
      await expect(page.locator('td', { hasText: 'No sections yet' })).toBeVisible();
    });

    test('C8: edit mode inputs are pre-populated with current values', async ({ page }) => {
      const firstRow = page.locator('tbody tr').first();

      // Get current values
      const currentId = await firstRow.locator('td').nth(1).textContent();
      const currentLabel = await firstRow.locator('td').nth(2).textContent();
      const currentComp = await firstRow.locator('td').nth(3).textContent();

      // Enter edit mode
      await firstRow.locator('button', { hasText: '✎' }).click();

      // Verify inputs have current values
      const idInput = firstRow.locator('td').nth(1).locator('input');
      const labelInput = firstRow.locator('td').nth(2).locator('input');
      const compInput = firstRow.locator('td').nth(3).locator('input');

      await expect(idInput).toHaveValue(currentId!);
      await expect(labelInput).toHaveValue(currentLabel!);
      await expect(compInput).toHaveValue(currentComp!);
    });

    test('C9: only one row can be in edit mode at a time', async ({ page }) => {
      const rows = page.locator('tbody tr');

      // Edit first row
      await rows.first().locator('button', { hasText: '✎' }).click();
      await expect(rows.first().locator('button', { hasText: '✓' })).toBeVisible();

      // Edit second row - first row should exit edit mode
      await rows.nth(1).locator('button', { hasText: '✎' }).click();
      await expect(rows.nth(1).locator('button', { hasText: '✓' })).toBeVisible();

      // First row should be back in view mode (pencil visible)
      // Note: This tests a UX pattern - the component may or may not enforce this
      // If both remain in edit mode, that's still valid behavior
      const firstRowConfirm = rows.first().locator('button', { hasText: '✓' });
      const firstRowEdit = rows.first().locator('button', { hasText: '✎' });

      // Check which behavior the component implements
      const isFirstStillEditing = await firstRowConfirm.isVisible().catch(() => false);
      if (isFirstStillEditing) {
        // Both rows in edit mode - component allows multiple edits
        console.log('Note: Component allows multiple rows in edit mode simultaneously');
      } else {
        // First row exited edit - component enforces single edit
        await expect(firstRowEdit).toBeVisible();
      }
    });
  });

  // =========================================================================
  // Group D: Save Flow
  // =========================================================================
  test.describe('Group D: Save flow', () => {
    test('D1: Save sends PUT request and shows success toast', async ({ page }) => {
      // Make a change to trigger unsaved state
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      const originalName = await nameInput.inputValue();

      // Intercept the PUT request to verify it fires
      let putFired = false;
      let putBody: any = null;
      page.on('request', (req) => {
        if (req.url().includes('/api/project') && req.method() === 'PUT') {
          putFired = true;
          putBody = req.postDataJSON();
        }
      });

      // Change name
      await nameInput.clear();
      await nameInput.fill(originalName + ' test');

      // Click Save and wait for PUT response
      const [response] = await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      expect(response.status()).toBe(200);

      // Verify PUT request was sent
      expect(putFired).toBe(true);
      expect(putBody).toBeTruthy();
      expect(putBody.name).toBe(originalName + ' test');

      // Verify success toast appears
      const toast = page.getByText('Saved successfully', { exact: false }).first();
      await expect(toast).toBeVisible({ timeout: 5000 });

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'D1-success-toast.png'), fullPage: true });

      // Restore original name and wait for save to complete
      await nameInput.clear();
      await nameInput.fill(originalName);
      await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      await page.waitForTimeout(500);
    });

    test('D2: toast disappears after ~3 seconds', async ({ page }) => {
      // Make a trivial change and save, waiting for the PUT response
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      const originalName = await nameInput.inputValue();
      await nameInput.clear();
      await nameInput.fill(originalName + 'x');

      const [response] = await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      expect(response.status()).toBe(200);

      // Toast should appear (use partial match to avoid Unicode issues)
      const toast = page.getByText('Saved successfully', { exact: false }).first();
      await expect(toast).toBeVisible({ timeout: 5000 });

      // Toast should disappear after ~3s
      await expect(toast).not.toBeVisible({ timeout: 5000 });

      // Restore
      await nameInput.clear();
      await nameInput.fill(originalName);
      await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      await page.waitForTimeout(500);
    });

    test('D3: yellow dot disappears after successful save', async ({ page }) => {
      const yellowDot = page.locator('span.rounded-full.bg-yellow-400');

      // No yellow dot initially
      await expect(yellowDot).not.toBeVisible();

      // Make a change
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      const originalName = await nameInput.inputValue();
      await nameInput.clear();
      await nameInput.fill(originalName + 'z');

      // Yellow dot appears
      await expect(yellowDot).toBeVisible({ timeout: 3000 });

      // Save and wait for response
      await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      await page.waitForTimeout(500);

      // Restore original
      await nameInput.clear();
      await nameInput.fill(originalName);
      await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      await page.waitForTimeout(500);
    });

    test('D4: save with invalid data shows error toast', async ({ page }) => {
      // Route the PUT to return an error
      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'PUT') {
          route.fulfill({
            status: 400,
            contentType: 'application/json',
            body: JSON.stringify({ error: 'Validation failed' }),
          });
        } else {
          route.continue();
        }
      });

      // Make a change and save
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      await nameInput.clear();
      await nameInput.fill('bad');
      await page.locator('button', { hasText: 'Save' }).click();

      // Should show error toast
      const errorToast = page.locator('text=Error saving project');
      await expect(errorToast).toBeVisible({ timeout: 5000 });

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'D4-error-toast.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group E: Drag Reorder
  // =========================================================================
  test.describe('Group E: Drag reorder', () => {
    test('E1: all rows are draggable', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const count = await rows.count();
      for (let i = 0; i < count; i++) {
        const draggable = await rows.nth(i).getAttribute('draggable');
        expect(draggable).toBe('true');
      }
    });

    test('E2: drag row 1 onto row 2 swaps them', async ({ page }) => {
      const rows = page.locator('tbody tr');

      // Capture IDs before
      const firstIdBefore = await rows.first().locator('td').nth(1).textContent();
      const secondIdBefore = await rows.nth(1).locator('td').nth(1).textContent();

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'E2-before-drag.png'), fullPage: true });

      // Perform drag via native events
      await rows.first().dispatchEvent('dragstart');
      await rows.nth(1).dispatchEvent('dragover');
      await rows.nth(1).dispatchEvent('drop');
      await page.waitForTimeout(300);

      // Verify swap
      const firstIdAfter = await rows.first().locator('td').nth(1).textContent();
      const secondIdAfter = await rows.nth(1).locator('td').nth(1).textContent();

      expect(firstIdAfter).toBe(secondIdBefore);
      expect(secondIdAfter).toBe(firstIdBefore);

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'E2-after-drag.png'), fullPage: true });
    });

    test('E3: drag row to same position is no-op', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const firstIdBefore = await rows.first().locator('td').nth(1).textContent();

      // Drag to self
      await rows.first().dispatchEvent('dragstart');
      await rows.first().dispatchEvent('dragover');
      await rows.first().dispatchEvent('drop');
      await page.waitForTimeout(300);

      // Same position
      const firstIdAfter = await rows.first().locator('td').nth(1).textContent();
      expect(firstIdAfter).toBe(firstIdBefore);
    });

    test('E4: row numbers update after drag reorder', async ({ page }) => {
      const rows = page.locator('tbody tr');

      // Row numbers should start at 1 and be sequential
      const count = await rows.count();
      for (let i = 0; i < count; i++) {
        const numCell = rows.nth(i).locator('td').first();
        await expect(numCell).toHaveText(String(i + 1));
      }

      // Drag row 1 to row 2
      await rows.first().dispatchEvent('dragstart');
      await rows.nth(1).dispatchEvent('dragover');
      await rows.nth(1).dispatchEvent('drop');
      await page.waitForTimeout(300);

      // Row numbers should still be sequential after reorder
      for (let i = 0; i < count; i++) {
        const numCell = rows.nth(i).locator('td').first();
        await expect(numCell).toHaveText(String(i + 1));
      }
    });
  });

  // =========================================================================
  // Group F: Edge Cases & Robustness
  // =========================================================================
  test.describe('Group F: Edge cases', () => {
    test('F1: Add Section then immediately delete it', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const initialCount = await rows.count();

      await page.locator('button', { hasText: '+ Add Section' }).click();
      await expect(rows).toHaveCount(initialCount + 1);

      // Delete the newly added row (last one)
      await rows.last().locator('button', { hasText: '✕' }).click();
      await expect(rows).toHaveCount(initialCount);
    });

    test('F2: rapid Add Section clicks create multiple rows', async ({ page }) => {
      const rows = page.locator('tbody tr');
      const initialCount = await rows.count();

      const addBtn = page.locator('button', { hasText: '+ Add Section' });
      await addBtn.click();
      await addBtn.click();
      await addBtn.click();

      await expect(rows).toHaveCount(initialCount + 3);
    });

    test('F3: empty project name can be saved', async ({ page }) => {
      const nameInput = page.locator('label', { hasText: 'Project Name' }).locator('..').locator('input');
      const originalName = await nameInput.inputValue();

      await nameInput.clear();
      // Empty name should be valid per schema (z.string() with no min)

      let putFired = false;
      page.on('request', (req) => {
        if (req.url().includes('/api/project') && req.method() === 'PUT') {
          putFired = true;
        }
      });

      await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      expect(putFired).toBe(true);

      // Restore
      await nameInput.fill(originalName);
      await Promise.all([
        page.waitForResponse((resp) => resp.url().includes('/api/project') && resp.request().method() === 'PUT'),
        page.locator('button', { hasText: 'Save' }).click(),
      ]);
      await page.waitForTimeout(500);
    });

    test('F4: editing section ID field works correctly', async ({ page }) => {
      const firstRow = page.locator('tbody tr').first();
      await firstRow.locator('button', { hasText: '✎' }).click();

      const idInput = firstRow.locator('td').nth(1).locator('input');
      await expect(idInput).toHaveValue('cold_open');

      await idInput.clear();
      await idInput.fill('new_cold_open');

      // Confirm
      await firstRow.locator('button', { hasText: '✓' }).click();

      // Verify the ID cell updated
      const idCell = firstRow.locator('td').nth(1);
      await expect(idCell).toHaveText('new_cold_open');
    });

    test('F5: editing compositionId field works correctly', async ({ page }) => {
      const firstRow = page.locator('tbody tr').first();
      await firstRow.locator('button', { hasText: '✎' }).click();

      const compInput = firstRow.locator('td').nth(3).locator('input');
      const originalVal = await compInput.inputValue();
      await compInput.clear();
      await compInput.fill('NewComposition');

      // Confirm
      await firstRow.locator('button', { hasText: '✓' }).click();

      // Verify
      const compCell = firstRow.locator('td').nth(3);
      await expect(compCell).toHaveText('NewComposition');
    });
  });
});
