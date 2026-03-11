import { test, expect } from '@playwright/test';
import { getProjectSections } from './helpers/project-fixtures';

const PROJECT_SECTIONS = getProjectSections();
const FIRST_SECTION = PROJECT_SECTIONS[0];
const SECOND_SECTION = PROJECT_SECTIONS[Math.min(1, PROJECT_SECTIONS.length - 1)];
const LAST_SECTION = PROJECT_SECTIONS[PROJECT_SECTIONS.length - 1];

test.describe('Stage 6: Spec Generation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Click on Spec Gen stage in sidebar
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
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
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible();
    await expect(page.locator('text=' + SECOND_SECTION.label).first()).toBeVisible();
    await expect(page.locator('text=' + LAST_SECTION.label).first()).toBeVisible();
  });

  test('section labels have readable dark text on white card (dark theme fix)', async ({ page }) => {
    // Bug fix: section toggle button text was white-on-white in dark theme.
    // After fix, it should have explicit dark text color (text-slate-800).
    const sectionBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
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
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });
    // The Regenerate button text includes a unicode arrow: "↺ Regenerate"
    const regenerateButtons = page.locator('button:has-text("Regenerate")');
    const count = await regenerateButtons.count();
    expect(count).toBeGreaterThanOrEqual(PROJECT_SECTIONS.length);
  });

  test('file table displays Type, Path, Status, Actions headers', async ({ page }) => {
    await expect(page.locator('th', { hasText: 'Type' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Path' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Status' }).first()).toBeVisible();
    await expect(page.locator('th', { hasText: 'Actions' }).first()).toBeVisible();
  });

  test('file status badges are visible for listed spec files', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });
    const statusBadges = page.locator('text=/^(exists|missing)$/');
    await expect(statusBadges.first()).toBeVisible();
    const count = await statusBadges.count();
    expect(count).toBeGreaterThanOrEqual(1);
  });

  test('spec file paths are visible in the table', async ({ page }) => {
    // Paths like "specs/00-cold-open/spec.md" should be visible
    await expect(page.locator('text=specs/').first()).toBeVisible();
  });

  test('accordion sections can collapse and expand', async ({ page }) => {
    // Sections use expanded state with ▾/▸ arrows. Find the first section toggle.
    const toggleBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
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
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(500);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
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
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

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
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

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
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

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
    // Wait for the stage to settle before scrolling (prevents "execution context destroyed" flakiness)
    await page.waitForLoadState('domcontentloaded');
    await expect(page.locator('h2', { hasText: 'Stage 6' })).toBeVisible({ timeout: 5000 });

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

  // ── New tests for known gaps ───────────────────────────────────────────────

  test('loading state shows "Loading spec list…" on initial mount', async ({ page }) => {
    // Navigate away and back to capture the loading state
    // Intercept the list API to slow it down so we can observe loading text
    await page.route('**/api/pipeline/specs/list', async (route) => {
      await new Promise((resolve) => setTimeout(resolve, 800));
      await route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ sections: [] }),
      });
    });

    // Navigate away then back to trigger fresh mount
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(300);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();

    // Loading text should appear immediately while API is in flight
    await expect(page.locator('text=Loading spec list…')).toBeVisible({ timeout: 2000 });
  });

  test('error state shows error message when specs/list API fails', async ({ page }) => {
    // Block the list API with an error response
    await page.route('**/api/pipeline/specs/list', (route) => {
      return route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    // Navigate away and back to trigger fresh load with error
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(300);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1500);

    // Error message should be visible
    await expect(page.locator('text=Error:').first()).toBeVisible({ timeout: 5000 });
  });

  test('localStorage persists accordion collapsed state across page reload', async ({ page }) => {
    // Wait for sections to load
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

    // Find the first section toggle button and ensure it's expanded (▾)
    const toggleBtn = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    const isExpanded = await toggleBtn.locator('text=▾').isVisible().catch(() => false);

    if (!isExpanded) {
      // Expand it first
      await toggleBtn.click();
      await page.waitForTimeout(300);
    }

    // Collapse the first section
    await toggleBtn.click();
    await page.waitForTimeout(300);
    await expect(toggleBtn.locator('text=▸')).toBeVisible();

    // Reload the page
    await page.reload();
    await page.waitForLoadState('networkidle');

    // Navigate back to Stage 6
    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1500);

    // The first section should still be collapsed (localStorage persisted)
    const toggleBtnAfter = page.locator('button', { hasText: FIRST_SECTION.label }).first();
    await expect(toggleBtnAfter).toBeVisible({ timeout: 10000 });
    await expect(toggleBtnAfter.locator('text=▸')).toBeVisible();
  });

  test('[Remotion] type badge renders with blue color class', async ({ page }) => {
    // Mock the spec list to include a file with firstLine = "[Remotion] Title Card"
    await page.route('**/api/pipeline/specs/list', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              id: 'cold-open',
              label: 'Cold Open',
              files: [
                { path: 'specs/00-cold-open/spec.md', exists: true, firstLine: '[Remotion] Title Card' },
              ],
            },
          ],
        }),
      });
    });

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(300);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // The badge should exist and have blue styling
    const badge = page.locator('span', { hasText: '[Remotion]' });
    await expect(badge).toBeVisible();
    const className = await badge.getAttribute('class');
    expect(className).toContain('blue');
  });

  test('[veo:] type badge renders with purple color class', async ({ page }) => {
    await page.route('**/api/pipeline/specs/list', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              id: 'cold-open',
              label: 'Cold Open',
              files: [
                { path: 'specs/00-cold-open/veo.md', exists: true, firstLine: '[veo:aerial-shot] flyover' },
              ],
            },
          ],
        }),
      });
    });

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(300);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // The badge should have purple styling
    const badge = page.locator('span').filter({ hasText: /\[veo:/ }).first();
    await expect(badge).toBeVisible();
    const className = await badge.getAttribute('class');
    expect(className).toContain('purple');
  });

  test('[title:] type badge renders with teal color class', async ({ page }) => {
    await page.route('**/api/pipeline/specs/list', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              id: 'cold-open',
              label: 'Cold Open',
              files: [
                { path: 'specs/00-cold-open/title.md', exists: true, firstLine: '[title:Part 1] Section Header' },
              ],
            },
          ],
        }),
      });
    });

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(300);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    // Component uses teal for [title:] badges (bg-teal-900/50 text-teal-300 border-teal-700)
    const badge = page.locator('span').filter({ hasText: /\[title:/ }).first();
    await expect(badge).toBeVisible();
    const className = await badge.getAttribute('class');
    expect(className).toContain('teal');
  });

  test('[split:] type badge renders with orange color class', async ({ page }) => {
    await page.route('**/api/pipeline/specs/list', (route) => {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          sections: [
            {
              id: 'cold-open',
              label: 'Cold Open',
              files: [
                { path: 'specs/00-cold-open/split.md', exists: true, firstLine: '[split:left] Left panel content' },
              ],
            },
          ],
        }),
      });
    });

    const sidebar = page.locator('aside');
    await sidebar.locator('button', { hasText: 'Setup' }).first().click();
    await page.waitForTimeout(300);
    await sidebar.locator('button', { hasText: 'Spec Gen' }).first().click();
    await page.waitForTimeout(1000);

    const badge = page.locator('span').filter({ hasText: /\[split:/ }).first();
    await expect(badge).toBeVisible();
    const className = await badge.getAttribute('class');
    expect(className).toContain('orange');
  });

  test('editor auto-save triggers PUT /api/pipeline/specs/file after blur (1s debounce)', async ({
    page,
  }) => {
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

    // Mock file GET
    await page.route('**/api/pipeline/specs/file**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: '# Original content' }),
        });
      }
      return route.fallback();
    });

    let putCalled = false;
    let putBody: unknown = null;

    await page.route('**/api/pipeline/specs/file', (route) => {
      if (route.request().method() === 'PUT') {
        putCalled = true;
        putBody = route.request().postDataJSON();
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ ok: true }),
        });
      }
      return route.fallback();
    });

    // Open the editor
    const editBtn = page.locator('button[title="Open in editor"]').first();
    await expect(editBtn).toBeVisible();
    await editBtn.click();
    await page.waitForTimeout(500);

    // Verify editor is open
    await expect(page.locator('text=Editing:').first()).toBeVisible();

    // Click into the editor and type
    const cmEditor = page.locator('.cm-editor').first();
    await cmEditor.click();
    await page.keyboard.type(' Modified');

    // Trigger blur by clicking outside the editor (on the heading)
    await page.locator('h2').first().click();

    // Wait for debounce (1s) + network round trip
    await page.waitForTimeout(1500);

    expect(putCalled).toBe(true);
    expect(putBody).toHaveProperty('path');
    expect(putBody).toHaveProperty('content');
  });

  test('"Saving…" indicator appears during auto-save and disappears after', async ({ page }) => {
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

    // Mock file GET
    await page.route('**/api/pipeline/specs/file**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: '# Content' }),
        });
      }
      return route.fallback();
    });

    // Slow the PUT to observe saving indicator
    await page.route('**/api/pipeline/specs/file', async (route) => {
      if (route.request().method() === 'PUT') {
        await new Promise((resolve) => setTimeout(resolve, 600));
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ ok: true }),
        });
      }
      return route.fallback();
    });

    // Open the editor
    const editBtn = page.locator('button[title="Open in editor"]').first();
    await editBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('text=Editing:').first()).toBeVisible();

    // Click editor and type, then blur by clicking outside
    const cmEditor = page.locator('.cm-editor').first();
    await cmEditor.click();
    await page.keyboard.type(' change');
    await page.locator('h2').first().click();

    // Wait for 1s debounce to fire, then saving indicator should appear while fetch is in flight
    await page.waitForTimeout(1200);
    await expect(page.locator('text=Saving…')).toBeVisible({ timeout: 500 });

    // After save completes (600ms fetch delay), indicator should disappear
    await expect(page.locator('text=Saving…')).not.toBeVisible({ timeout: 3000 });
  });

  test('CodeMirror editor text is visible (not white-on-white)', async ({ page }) => {
    // Bug: without theme="dark", CodeMirror uses a light (white) background but the
    // parent container is dark and global CSS makes text white → white text on white bg.
    await expect(page.locator('text=' + FIRST_SECTION.label).first()).toBeVisible({ timeout: 10000 });

    // Mock the file GET to return content we can check
    await page.route('**/api/pipeline/specs/file**', (route) => {
      if (route.request().method() === 'GET') {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ content: '# Spec Content\nSome text here' }),
        });
      }
      return route.fallback();
    });

    const editBtn = page.locator('button[title="Open in editor"]').first();
    await editBtn.click();
    await page.waitForTimeout(500);
    await expect(page.locator('text=Editing:').first()).toBeVisible();

    // The CodeMirror editor should NOT have white text on a white/light background.
    // Use .cm-editor background (the actual visual background) vs. .cm-content text color.
    const cmEditor = page.locator('.cm-editor').first();
    await expect(cmEditor).toBeVisible();

    const { editorBg, textColor } = await cmEditor.evaluate((el) => {
      const editorStyle = getComputedStyle(el);
      const content = el.querySelector('.cm-content');
      const contentStyle = content ? getComputedStyle(content) : null;
      return {
        editorBg: editorStyle.backgroundColor,
        textColor: contentStyle ? contentStyle.color : editorStyle.color,
      };
    });

    // Parse RGB values
    const parseRgb = (css: string) => {
      const m = css.match(/\d+/g);
      return m ? [Number(m[0]), Number(m[1]), Number(m[2])] : [0, 0, 0];
    };
    const [tr, tg, tb] = parseRgb(textColor);
    const [br, bg2, bb] = parseRgb(editorBg);

    // Text and background must not be the same color (catches white-on-white)
    const diff = Math.abs(tr - br) + Math.abs(tg - bg2) + Math.abs(tb - bb);
    expect(diff).toBeGreaterThan(100);
  });

  test('Generate All Specs SSE response sets jobId and activates log panel', async ({ page }) => {
    // The run endpoint returns SSE stream. The component should parse the stream
    // to extract the jobId from the "complete" event and pass it to SseLogPanel.
    // SseLogPanel then opens an EventSource to /api/jobs/{jobId}/stream.
    // If jobId is never set (old bug: res.json() on SSE), that EventSource call never happens.

    const TEST_JOB_ID = 'test-sse-job-42';

    // Mock the run endpoint to return a proper SSE stream
    await page.route('**/api/pipeline/specs/run', async (route) => {
      const sseBody = [
        `data: {"type":"log","message":"Starting generation..."}\n\n`,
        `data: {"type":"complete","jobId":"${TEST_JOB_ID}"}\n\n`,
      ].join('');
      return route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: sseBody,
      });
    });

    // Intercept the EventSource connection that SseLogPanel makes when jobId is set
    let jobStreamRequested = false;
    await page.route(`**/api/jobs/${TEST_JOB_ID}/stream`, (route) => {
      jobStreamRequested = true;
      return route.fulfill({
        status: 200,
        headers: { 'Content-Type': 'text/event-stream' },
        body: '',
      });
    });

    // Trigger Generate All
    const generateBtn = page.locator('button', { hasText: 'Generate All Specs' });
    await generateBtn.click();

    // Wait for SSE parsing + React re-render + EventSource creation
    await page.waitForTimeout(2000);

    // If the SSE parsing worked and jobId was set, SseLogPanel creates an EventSource
    // to /api/jobs/{TEST_JOB_ID}/stream — this is the proof that latestJobId was set.
    expect(jobStreamRequested).toBe(true);
  });
});
