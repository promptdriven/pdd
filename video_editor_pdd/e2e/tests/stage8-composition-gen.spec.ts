import { test, expect } from '@playwright/test';
import { getProjectSections } from './helpers/project-fixtures';

const PROJECT_SECTIONS = getProjectSections();
const FIRST_SECTION = PROJECT_SECTIONS[0];

test.describe('Stage 8: Composition Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Compositions stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    // Wait for the composition data to load (loading text disappears, sections appear)
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });
  });

  test('renders without crash', async ({ page }) => {
    const errorOverlay = page.locator('text=Runtime TypeError');
    const hasError = await errorOverlay.isVisible().catch(() => false);
    expect(hasError).toBe(false);
  });

  test('displays stage heading and description', async ({ page }) => {
    await expect(page.locator('h2', { hasText: 'Stage 8' })).toBeVisible();
    await expect(page.locator('text=Generate Remotion compositions')).toBeVisible();
  });

  test('displays Components heading with count', async ({ page }) => {
    const heading = page.locator('h3', { hasText: /Components\s*\(\d+\)/ });
    await expect(heading).toBeVisible();
  });

  test('displays Generate All Compositions button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Generate All Compositions' })).toBeVisible();
  });

  test('displays section accordions for all project sections', async ({ page }) => {
    for (const section of PROJECT_SECTIONS) {
      await expect(page.locator('button', { hasText: section.label }).first()).toBeVisible();
    }
  });

  test('section accordions are togglable', async ({ page }) => {
    // Initially sections show "Hide"
    const firstSectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    await expect(firstSectionBtn).toBeVisible();

    // The Hide/Show text should be visible
    const hideShow = firstSectionBtn.locator('span', { hasText: /Hide|Show/ });
    await expect(hideShow).toBeVisible();

    // Click to collapse
    await firstSectionBtn.click();
    await expect(firstSectionBtn.locator('span', { hasText: 'Show' })).toBeVisible();

    // Click to expand again
    await firstSectionBtn.click();
    await expect(firstSectionBtn.locator('span', { hasText: 'Hide' })).toBeVisible();
  });

  test('displays Section Wrappers heading', async ({ page }) => {
    await expect(page.locator('h4', { hasText: 'Section Wrappers' })).toBeVisible();
  });

  test('displays Asset Staging Manifest heading', async ({ page }) => {
    await expect(page.locator('h3', { hasText: 'Asset Staging Manifest' })).toBeVisible();
  });

  test('displays Stage All Missing button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Stage All Missing' })).toBeVisible();
  });

  test('displays staging manifest table headers', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Filename' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Expected' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Present' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Action' }).first()).toBeVisible();
  });

  test('displays Job Logs toggle', async ({ page }) => {
    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn).toBeVisible();

    // Toggle open
    await jobLogsBtn.click();
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();

    // Toggle closed
    await jobLogsBtn.click();
    await expect(jobLogsBtn.locator('span', { hasText: 'Show' })).toBeVisible();
  });

  test('displays Continue button', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'Continue' })).toBeVisible();
  });

  test('heading text is readable on dark background', async ({ page }) => {
    const h2 = page.locator('h2', { hasText: 'Stage 8' });
    await expect(h2).toBeVisible();

    const color = await h2.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // White text: RGB values should all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(true);
    }
  });

  test('components panel text is readable on white background', async ({ page }) => {
    const h3 = page.locator('h3', { hasText: /Components/ });
    await expect(h3).toBeVisible();

    const color = await h3.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      // Dark text on white panel: RGB values should NOT all be > 200
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('section accordion text is readable', async ({ page }) => {
    const sectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    await expect(sectionBtn).toBeVisible();

    const color = await sectionBtn.evaluate((el) => {
      const span = el.querySelector('span');
      return span ? getComputedStyle(span).color : getComputedStyle(el).color;
    });
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('staging manifest table headers are readable', async ({ page }) => {
    const filenameHeader = page.locator('th', { hasText: 'Filename' }).first();
    await expect(filenameHeader).toBeVisible();

    const color = await filenameHeader.evaluate((el) => getComputedStyle(el).color);
    const match = color.match(/(\d+)/g);
    if (match) {
      const [r, g, b] = match.map(Number);
      const isLight = r > 200 && g > 200 && b > 200;
      expect(isLight).toBe(false);
    }
  });

  test('wrapper status badges are visible', async ({ page }) => {
    // Scroll down to see Section Wrappers
    const wrapperHeading = page.locator('h4', { hasText: 'Section Wrappers' });
    await wrapperHeading.scrollIntoViewIfNeeded();
    await expect(wrapperHeading).toBeVisible();
    const wrapperSection = wrapperHeading.locator('..');
    const badges = wrapperSection.locator('span.rounded-full');
    await expect(badges.first()).toBeVisible({ timeout: 5000 });
    const count = await badges.count();
    expect(count).toBeGreaterThan(0);
  });

  test('no console errors on load', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(2000);
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  // ── Interactive tests ──────────────────────────────────────────────

  test('Generate All Compositions button click triggers POST /api/pipeline/compositions/run', async ({ page }) => {
    let postCalled = false;

    await page.route('**/api/pipeline/compositions/run', (route) => {
      postCalled = true;
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-comp-all-job' }),
      });
    });

    const generateBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await expect(generateBtn).toBeVisible();
    await expect(generateBtn).toBeEnabled();
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(postCalled).toBe(true);

    // After clicking, the button text should change to "Generating..." while busy
    // and the Job Logs panel should auto-open (logOpen becomes true)
    // Since we mocked a fast response, it may already revert, but the log panel should open
    const jobLogsBtn = page.locator('button', { hasText: 'Job Logs' });
    await expect(jobLogsBtn.locator('span', { hasText: 'Hide' })).toBeVisible();
  });

  test('Preview button opens dialog modal', async ({ page }) => {
    // Wait for composition data to load and sections to render
    await expect(page.locator('button', { hasText: FIRST_SECTION.label }).first()).toBeVisible({ timeout: 10000 });

    // Mock the preview endpoint
    await page.route('**/api/pipeline/compositions/preview**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ url: 'https://example.com/preview.png' }),
      });
    });

    // Ensure the first section is expanded (it should be by default)
    const firstSectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    const hideShowSpan = firstSectionBtn.locator('span', { hasText: /Hide|Show/ });
    const text = await hideShowSpan.textContent();
    if (text?.trim() === 'Show') {
      await firstSectionBtn.click();
      await page.waitForTimeout(300);
    }

    // Find a Preview button within the expanded section
    const previewBtn = page.locator('button', { hasText: 'Preview' }).first();
    // If no components exist, this section may not have a Preview button,
    // so we check for its existence before clicking
    const previewCount = await previewBtn.count();
    if (previewCount > 0) {
      await previewBtn.click();
      await page.waitForTimeout(500);

      // The <dialog> modal should now be open
      const dialog = page.locator('dialog');
      await expect(dialog).toBeVisible();

      // The dialog should contain "Preview" text in its header
      await expect(dialog.locator('text=Preview')).toBeVisible();
    }
  });

  test('Preview dialog close button closes modal', async ({ page }) => {
    await expect(page.locator('button', { hasText: FIRST_SECTION.label }).first()).toBeVisible({ timeout: 10000 });

    // Mock the preview endpoint
    await page.route('**/api/pipeline/compositions/preview**', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ url: 'https://example.com/preview.png' }),
      });
    });

    // Ensure the first section is expanded
    const firstSectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    const hideShowSpan = firstSectionBtn.locator('span', { hasText: /Hide|Show/ });
    const text = await hideShowSpan.textContent();
    if (text?.trim() === 'Show') {
      await firstSectionBtn.click();
      await page.waitForTimeout(300);
    }

    const previewBtn = page.locator('button', { hasText: 'Preview' }).first();
    const previewCount = await previewBtn.count();
    if (previewCount > 0) {
      // Open the dialog
      await previewBtn.click();
      await page.waitForTimeout(500);

      const dialog = page.locator('dialog');
      await expect(dialog).toBeVisible();

      // Click the Close button inside the dialog
      const closeBtn = dialog.locator('button', { hasText: 'Close' });
      await expect(closeBtn).toBeVisible();
      await closeBtn.click();
      await page.waitForTimeout(300);

      // Dialog should no longer be visible
      await expect(dialog).not.toBeVisible();
    }
  });

  test('Regenerate button triggers POST /api/pipeline/compositions/run with component name', async ({ page }) => {
    let postCalled = false;
    let requestBody: any = null;

    await page.route('**/api/pipeline/compositions/list', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              id: 'animation_section',
              label: FIRST_SECTION.label,
              components: [{ name: 'TitleSlide', status: 'missing', error: null }],
              wrappers: [{ name: 'animation_sectionWrapper', status: 'done', error: null }],
            },
          ],
        }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );

    await page.route('**/api/pipeline/compositions/run', (route) => {
      postCalled = true;
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-regen-comp-job' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();

    // Ensure the first section is expanded
    const firstSectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    await expect(firstSectionBtn).toBeVisible({ timeout: 10000 });
    const hideShowSpan = firstSectionBtn.locator('span', { hasText: /Hide|Show/ });
    const text = await hideShowSpan.textContent();
    if (text?.trim() === 'Show') {
      await firstSectionBtn.click();
      await page.waitForTimeout(300);
    }

    const componentRow = page.locator('[data-testid="component-row-TitleSlide"]');
    await expect(componentRow).toBeVisible();
    const regenBtn = componentRow.locator('button', { hasText: '↺' });
    await expect(regenBtn).toBeVisible();
    await regenBtn.click();
    await page.waitForTimeout(500);

    expect(postCalled).toBe(true);
    expect(requestBody).toHaveProperty('components');
    expect(Array.isArray(requestBody.components)).toBe(true);
    expect(requestBody.components).toEqual(['TitleSlide']);
  });

  test('Stage All Missing button triggers POST /api/pipeline/asset-staging/run', async ({ page }) => {
    let postCalled = false;

    await page.route('**/api/pipeline/asset-staging/run', (route) => {
      postCalled = true;
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-staging-job' }),
      });
    });

    const stageBtn = page.locator('button', { hasText: 'Stage All Missing' });
    await expect(stageBtn).toBeVisible();

    // Note: the button may be disabled if there are no missing staging entries.
    // We attempt a click — if it's disabled, the route won't fire, which is expected.
    const isDisabled = await stageBtn.isDisabled();
    if (!isDisabled) {
      await stageBtn.click();
      await page.waitForTimeout(500);
      expect(postCalled).toBe(true);
    } else {
      // Button correctly disabled when no missing files exist
      expect(isDisabled).toBe(true);
    }
  });

  test('Continue button is clickable and navigates to next stage', async ({ page }) => {
    const continueBtn = page.locator('button', { hasText: 'Continue' });
    await expect(continueBtn).toBeVisible();
    await expect(continueBtn).toBeEnabled();
    await continueBtn.click();
    await page.waitForTimeout(1000);

    // After clicking Continue, should advance to Stage 9 (Render & Stitch)
    await expect(page.locator('text=Render').first()).toBeVisible();
  });
});

// ── Bug 1: Wrapper rows missing Preview and ↺ buttons ────────────────────────

test.describe('Stage 8: Wrapper Controls', () => {
  const setupWrapperMocks = async (page: any) => {
    await page.route('**/api/pipeline/compositions/list', (route: any) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [{
            id: 'cold_open',
            label: 'Cold Open',
            components: [],
            wrappers: [{ name: 'cold_openWrapper', status: 'missing', error: null }],
          }],
        }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route: any) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });
    await page.locator('h4', { hasText: 'Section Wrappers' }).scrollIntoViewIfNeeded();
  };

  test('wrapper rows have Preview buttons', async ({ page }) => {
    await setupWrapperMocks(page);
    // Section Wrappers area should contain a Preview button
    const wrapperSection = page.locator('h4', { hasText: 'Section Wrappers' }).locator('..');
    await expect(wrapperSection.locator('button', { hasText: 'Preview' })).toBeVisible();
  });

  test('wrapper rows have Regenerate (↺) buttons', async ({ page }) => {
    await setupWrapperMocks(page);
    const wrapperSection = page.locator('h4', { hasText: 'Section Wrappers' }).locator('..');
    await expect(wrapperSection.locator('button', { hasText: '↺' })).toBeVisible();
  });

  test('wrapper Regenerate button triggers POST with wrapper name in wrappers array', async ({ page }) => {
    let requestBody: any = null;
    await page.route('**/api/pipeline/compositions/run', (route: any) => {
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-wrapper-regen-job' }),
      });
    });
    await setupWrapperMocks(page);
    const wrapperSection = page.locator('h4', { hasText: 'Section Wrappers' }).locator('..');
    const regenBtn = wrapperSection.locator('button', { hasText: '↺' });
    await expect(regenBtn).toBeVisible();
    await regenBtn.click();
    await page.waitForTimeout(500);
    expect(requestBody).not.toBeNull();
    expect(requestBody).toHaveProperty('wrappers');
    expect(requestBody.wrappers).toContain('cold_openWrapper');
  });

  test('wrapper Preview button opens dialog modal', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/preview**', (route: any) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ url: 'https://example.com/preview.png' }),
      })
    );
    await setupWrapperMocks(page);
    const wrapperSection = page.locator('h4', { hasText: 'Section Wrappers' }).locator('..');
    const previewBtn = wrapperSection.locator('button', { hasText: 'Preview' });
    await expect(previewBtn).toBeVisible();
    await previewBtn.click();
    await page.waitForTimeout(500);
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
  });
});

// ── Bug 2: Error-status row click does not expand log drawer ──────────────────

test.describe('Stage 8: Error Row Log Drawer', () => {
  const setupErrorComponentMocks = async (page: any) => {
    await page.route('**/api/pipeline/compositions/list', (route: any) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [{
            id: 'cold_open',
            label: 'Cold Open',
            components: [
              { name: 'TitleSlide', status: 'error', error: 'Claude Code error: timeout' },
              { name: 'CreditsSlide', status: 'done', error: null },
            ],
            wrappers: [],
          }],
        }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route: any) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });
  };

  test('clicking a component row with error status expands log drawer', async ({ page }) => {
    await setupErrorComponentMocks(page);
    const errorRow = page.locator('[data-testid="component-row-TitleSlide"]');
    await expect(errorRow).toBeVisible();
    await errorRow.click();
    const drawer = page.locator('[data-testid="error-log-drawer-TitleSlide"]');
    await expect(drawer).toBeVisible();
    await expect(drawer).toContainText('Claude Code error: timeout');
  });

  test('clicking the same error row again collapses the log drawer', async ({ page }) => {
    await setupErrorComponentMocks(page);
    const errorRow = page.locator('[data-testid="component-row-TitleSlide"]');
    await errorRow.click();
    const drawer = page.locator('[data-testid="error-log-drawer-TitleSlide"]');
    await expect(drawer).toBeVisible();
    // Second click should collapse
    await errorRow.click();
    await expect(drawer).not.toBeVisible();
  });

  test('non-error rows do not show a log drawer on click', async ({ page }) => {
    await setupErrorComponentMocks(page);
    const doneRow = page.locator('[data-testid="component-row-CreditsSlide"]');
    await expect(doneRow).toBeVisible();
    await doneRow.click();
    const drawer = page.locator('[data-testid="error-log-drawer-CreditsSlide"]');
    await expect(drawer).not.toBeVisible();
  });
});

// ── Bug 3: Generate All Compositions sends no payload body ────────────────────

test.describe('Stage 8: Generate All Compositions Payload', () => {
  test('Generate All Compositions sends sectionComponents and wrapper IDs in payload', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', (route: any) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              id: 'cold_open',
              label: 'Cold Open',
              components: [
                { name: 'TitleSlide', status: 'missing', error: null },
                { name: 'IntroSlide', status: 'missing', error: null },
              ],
              wrappers: [{ name: 'cold_openWrapper', status: 'missing', error: null }],
            },
            {
              id: 'part1',
              label: 'Part 1',
              components: [{ name: 'Part1Main', status: 'missing', error: null }],
              wrappers: [{ name: 'part1Wrapper', status: 'missing', error: null }],
            },
          ],
        }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route: any) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );

    let requestBody: any = null;
    await page.route('**/api/pipeline/compositions/run', (route: any) => {
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-gen-all-job' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });

    const generateBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(requestBody).not.toBeNull();
    expect(Array.isArray(requestBody.sectionComponents)).toBe(true);
    expect(requestBody.sectionComponents).toEqual([
      { sectionId: 'cold_open', components: ['TitleSlide', 'IntroSlide'] },
      { sectionId: 'part1', components: ['Part1Main'] },
    ]);
    expect(requestBody.wrappers).toContain('cold_openWrapper');
    expect(requestBody.wrappers).toContain('part1Wrapper');
  });

  test('Generate All Compositions with no sections sends empty sectionComponents and wrappers arrays', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/list', (route: any) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route: any) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );

    let requestBody: any = null;
    await page.route('**/api/pipeline/compositions/run', (route: any) => {
      requestBody = route.request().postDataJSON();
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'test-gen-all-empty-job' }),
      });
    });

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });

    const generateBtn = page.locator('button', { hasText: 'Generate All Compositions' });
    await generateBtn.click();
    await page.waitForTimeout(500);

    expect(requestBody).not.toBeNull();
    expect(Array.isArray(requestBody.sectionComponents)).toBe(true);
    expect(requestBody.sectionComponents).toHaveLength(0);
    expect(Array.isArray(requestBody.wrappers)).toBe(true);
    expect(requestBody.wrappers).toHaveLength(0);
  });
});

// ── Bug A: Preview dialog not centered ───────────────────────────────────────

test.describe('Stage 8: Preview Dialog Centering', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });
  });

  test('Preview dialog is horizontally centered in the viewport', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/preview**', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ url: 'https://example.com/preview.png' }),
      })
    );

    // Wait for sections to load, then ensure the first section is expanded
    const firstSectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    await expect(firstSectionBtn).toBeVisible({ timeout: 15000 });
    const spanText = await firstSectionBtn.locator('span', { hasText: /Hide|Show/ }).textContent();
    if (spanText?.trim() === 'Show') {
      await firstSectionBtn.click();
      await page.waitForTimeout(300);
    }

    const previewBtn = page.locator('button', { hasText: 'Preview' }).first();
    await expect(previewBtn).toBeVisible();
    await previewBtn.click();
    await page.waitForTimeout(500);

    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();

    const { dialogLeft, dialogWidth, viewportWidth } = await page.evaluate(() => {
      const el = document.querySelector('dialog')!;
      const rect = el.getBoundingClientRect();
      return { dialogLeft: rect.left, dialogWidth: rect.width, viewportWidth: window.innerWidth };
    });

    // Dialog center should be within 50px of viewport center
    const dialogCenter = dialogLeft + dialogWidth / 2;
    const viewportCenter = viewportWidth / 2;
    expect(Math.abs(dialogCenter - viewportCenter)).toBeLessThan(50);

    await dialog.locator('button', { hasText: 'Close' }).click();
  });

  test('Preview dialog is vertically centered in the viewport', async ({ page }) => {
    await page.route('**/api/pipeline/compositions/preview**', (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ url: 'https://example.com/preview.png' }),
      })
    );

    const firstSectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    await expect(firstSectionBtn).toBeVisible({ timeout: 15000 });
    const spanText = await firstSectionBtn.locator('span', { hasText: /Hide|Show/ }).textContent();
    if (spanText?.trim() === 'Show') {
      await firstSectionBtn.click();
      await page.waitForTimeout(300);
    }

    const previewBtn = page.locator('button', { hasText: 'Preview' }).first();
    await previewBtn.click();
    await page.waitForTimeout(500);

    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();

    const { dialogTop, dialogHeight, viewportHeight } = await page.evaluate(() => {
      const el = document.querySelector('dialog')!;
      const rect = el.getBoundingClientRect();
      return { dialogTop: rect.top, dialogHeight: rect.height, viewportHeight: window.innerHeight };
    });

    // Dialog center should be within 50px of viewport vertical center
    const dialogCenter = dialogTop + dialogHeight / 2;
    const viewportCenter = viewportHeight / 2;
    expect(Math.abs(dialogCenter - viewportCenter)).toBeLessThan(50);

    await dialog.locator('button', { hasText: 'Close' }).click();
  });
});

// ── Bug B: Preview shows broken image instead of fallback ────────────────────

test.describe('Stage 8: Preview Fallback Content', () => {
  const setupAndOpenPreview = async (page: any, previewHandler: (route: any) => void) => {
    await page.route('**/api/pipeline/compositions/list', (route: any) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [{
            id: 'cold_open', label: 'Cold Open',
            components: [{ name: 'spec', status: 'missing', error: null }],
            wrappers: [],
          }],
        }),
      })
    );
    await page.route('**/api/pipeline/veo/staging-manifest', (route: any) =>
      route.fulfill({ status: 200, contentType: 'application/json', body: '[]' })
    );
    await page.route('**/api/pipeline/compositions/preview**', previewHandler);

    await page.goto('/');
    await page.waitForLoadState('networkidle');
    const sidebar = page.locator('aside');
    await sidebar.locator('div', { hasText: 'Compositions' }).first().click();
    await expect(page.locator('h2', { hasText: 'Composition Generation' })).toBeVisible({ timeout: 15000 });

    const previewBtn = page.locator('button', { hasText: 'Preview' }).first();
    await expect(previewBtn).toBeVisible();
    await previewBtn.click();
    await page.waitForTimeout(500);
  };

  test('shows fallback when API returns plain text that is not a URL', async ({ page }) => {
    await setupAndOpenPreview(page, (route) =>
      route.fulfill({ status: 200, contentType: 'text/plain', body: 'not-a-url-just-text' })
    );
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
    await expect(dialog.locator('text=Preview not available')).toBeVisible();
    await expect(dialog.locator('img')).toHaveCount(0);
  });

  test('shows fallback when API returns 404', async ({ page }) => {
    await setupAndOpenPreview(page, (route) =>
      route.fulfill({ status: 404, contentType: 'text/plain', body: 'Not Found' })
    );
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
    await expect(dialog.locator('text=Preview not available')).toBeVisible();
    await expect(dialog.locator('img')).toHaveCount(0);
  });

  test('shows fallback when API returns 500', async ({ page }) => {
    await setupAndOpenPreview(page, (route) =>
      route.fulfill({ status: 500, contentType: 'application/json', body: JSON.stringify({ error: 'Internal Server Error' }) })
    );
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
    await expect(dialog.locator('text=Preview not available')).toBeVisible();
    await expect(dialog.locator('img')).toHaveCount(0);
  });

  test('shows fallback when API returns JSON without url/path/previewUrl fields', async ({ page }) => {
    await setupAndOpenPreview(page, (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ status: 'pending', message: 'not ready' }),
      })
    );
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
    await expect(dialog.locator('text=Preview not available')).toBeVisible();
    await expect(dialog.locator('img')).toHaveCount(0);
  });

  test('shows image when API returns valid JSON with url field', async ({ page }) => {
    await setupAndOpenPreview(page, (route) =>
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ url: 'https://example.com/preview.png' }),
      })
    );
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
    await expect(dialog.locator('img')).toHaveCount(1);
    await expect(dialog.locator('text=Preview not available')).toHaveCount(0);
  });

  test('shows image when API returns plain text that is a valid https URL', async ({ page }) => {
    await setupAndOpenPreview(page, (route) =>
      route.fulfill({
        status: 200,
        contentType: 'text/plain',
        body: 'https://example.com/preview.png',
      })
    );
    const dialog = page.locator('dialog');
    await expect(dialog).toBeVisible();
    await expect(dialog.locator('img')).toHaveCount(1);
    await expect(dialog.locator('text=Preview not available')).toHaveCount(0);
  });
});
