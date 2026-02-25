import { test, expect } from '@playwright/test';

test.describe('Stage 6: Spec Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Spec Gen stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);
  });

  test('renders without crash', async ({ page }) => {
    // No runtime error overlay should appear
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays stage heading', async ({ page }) => {
    const heading = page.locator('h2', { hasText: 'Stage 6' });
    await expect(heading).toBeVisible();
    await expect(heading).toContainText('Spec Generation');
  });

  test('displays Generate All Specs button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate All Specs' })).toBeVisible();
  });

  test('displays Continue button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Continue' })).toBeVisible();
  });

  test('renders section accordion cards from project.json', async ({ page }) => {
    // The project has 7 sections; each should appear as a card with its label
    await expect(page.locator('text=Cold Open').first()).toBeVisible();
    await expect(page.locator('text=Part 1: Economics').first()).toBeVisible();
    await expect(page.locator('text=Closing').first()).toBeVisible();
  });

  test('section labels have readable dark text on white card (dark theme fix)', async ({ page }) => {
    // Bug fix: section toggle button text was white-on-white in dark theme.
    // After fix, it should have explicit dark text color (text-slate-800).
    const sectionBtn = page.locator('button', { hasText: 'Cold Open' }).first();
    await expect(sectionBtn).toBeVisible();

    const color = await sectionBtn.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Dark text: RGB values should NOT all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('each section has a Regenerate button', async ({ page }) => {
    // Wait for section data to load (Loading spec list... disappears)
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });
    // The Regenerate button text includes a unicode arrow: "↺ Regenerate"
    const regenerateButtons = page.locator('button:has-text("Regenerate")');
    const count = await regenerateButtons.count();
    expect(count).toBeGreaterThanOrEqual(7);
  });

  test('file table displays Type, Path, Status, Actions headers', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Type' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Path' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Status' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Actions' }).first()).toBeVisible();
  });

  test('file status shows missing when spec files do not exist', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });
    // All spec files are "missing" since specs/ directory is empty
    const missingBadges = page.locator('text=missing');
    await expect(missingBadges.first()).toBeVisible();
    const count = await missingBadges.count();
    expect(count).toBeGreaterThanOrEqual(1);
  });

  test('spec file paths are visible in the table', async ({ page }) => {
    // Paths like "specs/00-cold-open/spec.md" should be visible
    await expect(page.locator('text=specs/').first()).toBeVisible();
  });

  test('accordion sections can collapse and expand', async ({ page }) => {
    // Sections use expanded state with ▾/▸ arrows. Find the first section toggle.
    const toggleBtn = page.locator('button', { hasText: 'Cold Open' }).first();
    await expect(toggleBtn).toBeVisible();

    // Check if section is currently expanded (▾ arrow visible)
    const isExpanded = await toggleBtn.locator('text=▾').isVisible().catch(() => false);

    if (isExpanded) {
      // Collapse it
      await toggleBtn.click();
      await page.waitForTimeout(300);
      // The ▸ arrow should now be visible (collapsed)
      await expect(toggleBtn.locator('text=▸')).toBeVisible();

      // Expand it again
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▾')).toBeVisible();
    } else {
      // Expand it
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▾')).toBeVisible();

      // Collapse it
      await toggleBtn.click();
      await page.waitForTimeout(300);
      await expect(toggleBtn.locator('text=▸')).toBeVisible();
    }
  });

  test('Spec Generation Logs details element is present', async ({ page }) => {
    await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
    await page.waitForTimeout(300);
    const logsSummary = page.locator('summary', { hasText: 'Spec Generation Logs' });
    await expect(logsSummary).toBeVisible();
  });

  test('no console errors on load', async ({ page }) => {
    // This test uses the beforeEach navigation (already on Stage 6).
    // We just verify no page errors were captured.
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Re-click on Stage 6 to trigger a fresh load within the already-loaded page
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);
    await sidebar.locator('div', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(2000);

    // Filter out non-application errors
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  // ── Interactive tests ──────────────────────────────────────────────

  test('Generate All Specs button click triggers POST /api/pipeline/specs/run', async ({ page }) => {
    let postCalled = false;
    let requestBody: any = null;

    await page.route('**/api/pipeline/specs/run', (route) => {
      postCalled = true;
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-spec-job-1' }),
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate All Specs' });
    await expect(generateBtn).toBeVisible();
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(postCalled).toBe(true);
    // Generate All sends an empty payload (no section filter)
    expect(requestBody).toEqual({});
  });

  test('Edit button opens inline CodeMirror editor', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });

    // Mock the file content endpoint
    await page.route('**/api/pipeline/specs/file**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: '# Test spec content\nSome markdown here' }),
        });
      }
      return route.fallback();
    });

    // The edit button is the pencil icon "✎" in the Actions column
    const editBtn = page.locator('button[title="Open in editor"]').first();
    await expect(editBtn).toBeVisible();
    await editBtn.click();
    await page.waitForTimeout(500);

    // After clicking edit, a CodeMirror editor should appear with "Editing:" title
    await expect(page.locator('text=Editing:').first()).toBeVisible();

    // The CodeMirror editor container should be present
    const cmEditor = page.locator('.cm-editor');
    await expect(cmEditor.first()).toBeVisible();
  });

  test('File regenerate button triggers POST /api/pipeline/specs/run with file path', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });

    let postCalled = false;
    let requestBody: any = null;

    await page.route('**/api/pipeline/specs/run', (route) => {
      postCalled = true;
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-regen-file-job' }),
      });
    });

    // The file regenerate button is the "↺" icon in the Actions column (second button per row)
    const fileRegenBtn = page.locator('button[title="Regenerate file"]').first();
    await expect(fileRegenBtn).toBeVisible();
    await fileRegenBtn.click();
    await page.waitForTimeout(500);

    expect(postCalled).toBe(true);
    // File regeneration sends { files: [filePath] }
    expect(requestBody).toHaveProperty('files');
    expect(Array.isArray(requestBody.files)).toBe(true);
    expect(requestBody.files.length).toBe(1);
  });

  test('Section regenerate button triggers POST /api/pipeline/specs/run with section id', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=Cold Open').first()).toBeVisible({ timeout: 10000 });

    let postCalled = false;
    let requestBody: any = null;

    await page.route('**/api/pipeline/specs/run', (route) => {
      postCalled = true;
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-regen-section-job' }),
      });
    });

    // The section-level Regenerate button contains "↺ Regenerate"
    const sectionRegenBtn = page.locator('button', { hasText: '↺ Regenerate' }).first();
    await expect(sectionRegenBtn).toBeVisible();
    await sectionRegenBtn.click();
    await page.waitForTimeout(500);

    expect(postCalled).toBe(true);
    // Section regeneration sends { sections: [sectionId] }
    expect(requestBody).toHaveProperty('sections');
    expect(Array.isArray(requestBody.sections)).toBe(true);
    expect(requestBody.sections.length).toBe(1);
  });

  test('Continue button is clickable and navigates to next stage', async ({ page }) => {
    const continueBtn = page.locator('button', { hasText: 'Continue' });
    await expect(continueBtn).toBeVisible();
    await expect(continueBtn).toBeEnabled();
    await continueBtn.click();
    await page.waitForTimeout(1000);

    // After clicking Continue, we should advance to Stage 7 (Veo Gen)
    // The Veo Gen content or heading should become visible
    await expect(page.locator('text=Veo').first()).toBeVisible();
  });

  test('Logs accordion opens and closes', async ({ page }) => {
    // Scroll to the bottom to find the logs <details> element
    await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
    await page.waitForTimeout(300);

    const logsSummary = page.locator('summary', { hasText: 'Spec Generation Logs' });
    await expect(logsSummary).toBeVisible();

    // Initially the <details> should be closed (no <SseLogPanel> content visible inside)
    const detailsEl = page.locator('details', { has: logsSummary });
    const isOpenBefore = await detailsEl.getAttribute('open');
    // When closed, the "open" attribute should not be present
    expect(isOpenBefore).toBeNull();

    // Click to open
    await logsSummary.click();
    await page.waitForTimeout(300);

    // After clicking, the <details> should have the "open" attribute
    const isOpenAfter = await detailsEl.getAttribute('open');
    expect(isOpenAfter).not.toBeNull();

    // Click again to close
    await logsSummary.click();
    await page.waitForTimeout(300);

    const isOpenFinal = await detailsEl.getAttribute('open');
    expect(isOpenFinal).toBeNull();
  });
});
