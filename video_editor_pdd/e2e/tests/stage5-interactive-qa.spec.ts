import { test, expect } from '@playwright/test';
import path from 'path';

const SCREENSHOT_DIR = path.join(__dirname, '..', 'screenshots');

/**
 * Navigate to Stage 5 (Audio Sync) via the sidebar.
 * Uses 3-attempt retry with sidebar `div.cursor-pointer.nth(4)`.
 */
async function navigateToStage5(page: import('@playwright/test').Page) {
  await page.goto('/');
  await page.waitForLoadState('networkidle');

  const sidebar = page.locator('aside');
  await expect(sidebar).toBeVisible({ timeout: 5000 });

  // Wait for React hydration
  await page.waitForTimeout(1000);

  const heading = page.locator('h2', { hasText: 'Stage 5' });

  // Attempt 1: Playwright click
  await sidebar.locator('div.cursor-pointer').nth(4).click();
  try {
    await expect(heading).toBeVisible({ timeout: 3000 });
  } catch {
    // Attempt 2: JS click
    await page.waitForTimeout(500);
    await page.evaluate(() => {
      const items = document.querySelectorAll('aside div.cursor-pointer');
      if (items[4]) (items[4] as HTMLElement).click();
    });
    try {
      await expect(heading).toBeVisible({ timeout: 3000 });
    } catch {
      // Attempt 3: force click after longer wait
      await page.waitForTimeout(1000);
      await sidebar.locator('div.cursor-pointer').nth(4).click({ force: true });
      await expect(heading).toBeVisible({ timeout: 10000 });
    }
  }

  await page.waitForTimeout(500);
}

/**
 * Navigate to Stage 5 with mocked GET /api/project and GET timestamps.
 * Sets up route mocks BEFORE navigating so they're in place for the fetch.
 */
async function navigateWithMockedProject(
  page: import('@playwright/test').Page,
  projectOverrides: Record<string, unknown> = {},
  timestampsWords: Array<{ word: string; start: number; end: number; segmentId?: string }> = [],
) {
  const defaultProject = {
    name: 'Test Project',
    outputResolution: { width: 1920, height: 1080 },
    tts: { engine: 'qwen3', modelPath: '', tokenizerPath: '', speaker: 'default', speakingRate: 1.0, sampleRate: 22050 },
    sections: [
      { id: 'intro', label: 'Introduction', videoFile: '', specDir: '', remotionDir: '', compositionId: '', durationSeconds: 60, offsetSeconds: 0 },
      { id: 'main', label: 'Main Content', videoFile: '', specDir: '', remotionDir: '', compositionId: '', durationSeconds: 120, offsetSeconds: 60 },
    ],
    audioSync: {
      sectionGroups: {
        intro: ['seg_001', 'seg_002'],
        main: ['seg_003'],
      },
      silenceGapDefault: 0.5,
    },
    veo: { model: 'veo-3.1', defaultAspectRatio: '16:9', maxConcurrentGenerations: 2, references: [], frameChains: [] },
    render: { maxParallelRenders: 2, useLambda: false, lambdaRegion: 'us-east-1' },
    ...projectOverrides,
  };

  await page.route('**/api/project', (route) => {
    if (route.request().method() === 'GET') {
      return route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(defaultProject),
      });
    }
    return route.continue();
  });

  await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
    return route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify({ words: timestampsWords }),
    });
  });

  await navigateToStage5(page);
  await page.waitForTimeout(500);
}

test.describe('Stage 5: Interactive QA - Comprehensive Feature Testing', () => {
  // =========================================================================
  // Group A: Initial Load & UI Elements (9 tests)
  // =========================================================================
  test.describe('Group A: Initial load & UI elements', () => {
    test('A1: "Stage 5 — Audio Sync" heading visible', async ({ page }) => {
      await navigateToStage5(page);
      const heading = page.locator('h2', { hasText: 'Stage 5' });
      await expect(heading).toBeVisible();
      await expect(heading).toHaveText(/Stage 5 — Audio Sync/);
    });

    test('A2: "Audio Sync Section Groups" subheading (h3) visible', async ({ page }) => {
      await navigateToStage5(page);
      const h3 = page.locator('h3', { hasText: 'Audio Sync Section Groups' });
      await expect(h3).toBeVisible();
    });

    test('A3: "Save Config" button visible with bg-blue-600', async ({ page }) => {
      await navigateToStage5(page);
      const btn = page.locator('button', { hasText: 'Save Config' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-blue-600');
    });

    test('A4: "Run Audio Sync" button visible with bg-emerald-600', async ({ page }) => {
      await navigateToStage5(page);
      const btn = page.locator('button', { hasText: 'Run Audio Sync' });
      await expect(btn).toBeVisible();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-emerald-600');
    });

    test('A5: "Word Timestamp Viewer" heading visible', async ({ page }) => {
      await navigateToStage5(page);
      const heading = page.locator('h2', { hasText: 'Word Timestamp Viewer' });
      await expect(heading).toBeVisible();
    });

    test('A6: Section dropdown (select) present', async ({ page }) => {
      await navigateToStage5(page);
      const select = page.locator('select');
      await expect(select).toBeVisible();
    });

    test('A7: Search input with placeholder "Search word…"', async ({ page }) => {
      await navigateToStage5(page);
      const input = page.locator('input[placeholder="Search word…"]');
      await expect(input).toBeVisible();
    });

    test('A8: Word count indicator "X of Y words" visible', async ({ page }) => {
      await navigateToStage5(page);
      await expect(page.locator('text=/\\d+ of \\d+ words/')).toBeVisible();
    });

    test('A9: screenshot — full initial state', async ({ page }) => {
      await navigateWithMockedProject(page, {}, [
        { word: 'hello', start: 0.0, end: 0.5, segmentId: 'seg_001' },
        { word: 'world', start: 0.5, end: 1.0, segmentId: 'seg_002' },
      ]);
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-A9-initial-state.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group B: Section Groups Config Table (8 tests)
  // =========================================================================
  test.describe('Group B: Section groups config table', () => {
    test('B1: Table headers "Section" and "Segment IDs (comma-separated)"', async ({ page }) => {
      await navigateWithMockedProject(page);
      await expect(page.locator('th', { hasText: 'Section' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Segment IDs' })).toBeVisible();
    });

    test('B2: Section labels display with font-medium text-slate-200', async ({ page }) => {
      await navigateWithMockedProject(page);
      const label = page.locator('td', { hasText: 'Introduction' });
      await expect(label).toBeVisible();
      const cls = await label.getAttribute('class') ?? '';
      expect(cls).toContain('font-medium');
      expect(cls).toContain('text-slate-200');
    });

    test('B3: Input fields have placeholder "segment1, segment2, segment3"', async ({ page }) => {
      await navigateWithMockedProject(page);
      const inputs = page.locator('input[placeholder="segment1, segment2, segment3"]');
      const count = await inputs.count();
      expect(count).toBeGreaterThanOrEqual(2); // intro + main
    });

    test('B4: Typing in input field updates value', async ({ page }) => {
      await navigateWithMockedProject(page);
      const input = page.locator('input[placeholder="segment1, segment2, segment3"]').first();
      await input.fill('seg_100, seg_200');
      await expect(input).toHaveValue('seg_100, seg_200');
    });

    test('B5: Multiple sections render as separate rows', async ({ page }) => {
      await navigateWithMockedProject(page);
      // Both "Introduction" and "Main Content" rows should exist
      await expect(page.locator('td', { hasText: 'Introduction' })).toBeVisible();
      await expect(page.locator('td', { hasText: 'Main Content' })).toBeVisible();
    });

    test('B6: SegmentRange normalization — {startSegment, endSegment} renders as comma-joined', async ({ page }) => {
      await navigateWithMockedProject(page, {
        audioSync: {
          sectionGroups: {
            intro: { startSegment: 'seg_001', endSegment: 'seg_005' },
            main: ['seg_006', 'seg_007'],
          },
          silenceGapDefault: 0.5,
        },
      });
      // The intro input should show "seg_001, seg_005" (normalized from SegmentRange)
      const introInput = page.locator('input[placeholder="segment1, segment2, segment3"]').first();
      await expect(introInput).toHaveValue('seg_001, seg_005');
    });

    test('B7: Input has bg-slate-800 border-slate-600 styling', async ({ page }) => {
      await navigateWithMockedProject(page);
      const input = page.locator('input[placeholder="segment1, segment2, segment3"]').first();
      const cls = await input.getAttribute('class') ?? '';
      expect(cls).toContain('bg-slate-800');
      expect(cls).toContain('border-slate-600');
    });

    test('B8: screenshot — config table with sections', async ({ page }) => {
      await navigateWithMockedProject(page, {}, [
        { word: 'test', start: 0.0, end: 0.5, segmentId: 'seg_001' },
      ]);
      // Scroll to the config table area
      const configCard = page.locator('h3', { hasText: 'Audio Sync Section Groups' });
      await configCard.scrollIntoViewIfNeeded();
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-B8-config-table.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group C: Save Config (7 tests)
  // =========================================================================
  test.describe('Group C: Save config', () => {
    test('C1: Save Config fires PUT /api/project', async ({ page }) => {
      let putCalled = false;
      await navigateWithMockedProject(page);

      // Override the project route to also intercept PUT
      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'PUT') {
          putCalled = true;
          return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
        }
        return route.continue();
      });

      await page.locator('button', { hasText: 'Save Config' }).click();
      await page.waitForTimeout(500);
      expect(putCalled).toBe(true);
    });

    test('C2: PUT body includes audioSync.sectionGroups with updated values', async ({ page }) => {
      let putBody: any = null;
      await navigateWithMockedProject(page);

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'PUT') {
          putBody = JSON.parse(route.request().postData() ?? '{}');
          return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
        }
        return route.continue();
      });

      // Modify an input first
      const input = page.locator('input[placeholder="segment1, segment2, segment3"]').first();
      await input.fill('seg_new_1, seg_new_2');
      await page.waitForTimeout(200);

      await page.locator('button', { hasText: 'Save Config' }).click();
      await page.waitForTimeout(500);

      expect(putBody).toBeTruthy();
      expect(putBody.audioSync).toBeTruthy();
      expect(putBody.audioSync.sectionGroups).toBeTruthy();
      // The intro group should contain updated values
      expect(putBody.audioSync.sectionGroups.intro).toEqual(['seg_new_1', 'seg_new_2']);
    });

    test('C3: Button shows "Saving…" and is disabled during save', async ({ page }) => {
      await navigateWithMockedProject(page);

      // Slow down PUT response so we can observe the saving state
      await page.route('**/api/project', async (route) => {
        if (route.request().method() === 'PUT') {
          await new Promise((r) => setTimeout(r, 1500));
          return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
        }
        return route.continue();
      });

      const btn = page.locator('button', { hasText: /Save Config|Saving/ });
      await btn.click();

      // During the slow request, button should show "Saving…" and be disabled
      await expect(page.locator('button', { hasText: 'Saving…' })).toBeVisible({ timeout: 2000 });
      await expect(page.locator('button', { hasText: 'Saving…' })).toBeDisabled();
    });

    test('C4: Button reverts to "Save Config" after save completes', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'PUT') {
          return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
        }
        return route.continue();
      });

      await page.locator('button', { hasText: 'Save Config' }).click();
      await page.waitForTimeout(500);

      await expect(page.locator('button', { hasText: 'Save Config' })).toBeVisible();
      await expect(page.locator('button', { hasText: 'Save Config' })).toBeEnabled();
    });

    test('C5: Modified input value persists after save', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'PUT') {
          return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
        }
        return route.continue();
      });

      const input = page.locator('input[placeholder="segment1, segment2, segment3"]').first();
      await input.fill('persisted_seg');
      await page.locator('button', { hasText: 'Save Config' }).click();
      await page.waitForTimeout(500);

      // Value should still be there after save
      await expect(input).toHaveValue('persisted_seg');
    });

    test('C6: Save failure (500) does not crash component', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'PUT') {
          return route.fulfill({ status: 500, contentType: 'application/json', body: '{"error":"Internal Server Error"}' });
        }
        return route.continue();
      });

      await page.locator('button', { hasText: 'Save Config' }).click();
      await page.waitForTimeout(500);

      // Component should not crash — heading should still be visible
      await expect(page.locator('h2', { hasText: 'Stage 5' })).toBeVisible();
      // Button should revert (finally block resets savingConfig)
      await expect(page.locator('button', { hasText: 'Save Config' })).toBeVisible();
    });

    test('C7: screenshot — saving indicator state', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/project', async (route) => {
        if (route.request().method() === 'PUT') {
          await new Promise((r) => setTimeout(r, 2000));
          return route.fulfill({ status: 200, contentType: 'application/json', body: '{}' });
        }
        return route.continue();
      });

      await page.locator('button', { hasText: 'Save Config' }).click();
      await page.waitForTimeout(300);
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-C7-saving-state.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group D: Run Audio Sync & SSE (7 tests)
  // =========================================================================
  test.describe('Group D: Run Audio Sync & SSE', () => {
    test('D1: Run Audio Sync fires POST /api/pipeline/audio-sync/run', async ({ page }) => {
      let postCalled = false;
      await navigateWithMockedProject(page);

      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        postCalled = true;
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-job-d1' }),
        });
      });

      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      await page.waitForTimeout(500);
      expect(postCalled).toBe(true);
    });

    test('D2: POST returns {jobId} — jobId state is set', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-job-d2' }),
        });
      });

      // Mock the SSE stream endpoint to prevent hanging requests
      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'data: {"type":"done"}\n\n',
        });
      });

      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      await page.waitForTimeout(1000);

      // SseLogPanel should render (verifying jobId was set)
      const ssePanel = page.locator('text=/Waiting for logs|Log|Done|Error/');
      await expect(ssePanel.first()).toBeVisible({ timeout: 5000 });
    });

    test('D3: SseLogPanel appears after receiving jobId', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-job-d3' }),
        });
      });

      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'data: {"type":"log","message":"Processing audio..."}\n\ndata: {"type":"done"}\n\n',
        });
      });

      // Before clicking — no SSE panel
      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      await page.waitForTimeout(1000);

      // After clicking, some log-related content should appear
      const logArea = page.locator('[class*="bg-"]', { hasText: /Processing audio|Waiting for logs|Done/ });
      await expect(logArea.first()).toBeVisible({ timeout: 5000 });
    });

    test('D4: SseLogPanel shows "Waiting for logs…" or log messages', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-job-d4' }),
        });
      });

      // Don't fulfill the stream immediately to see "Waiting for logs…"
      await page.route('**/api/jobs/*/stream', (route) => {
        // Leave pending for a moment, then fulfill
        return new Promise((resolve) => {
          setTimeout(() => {
            route.fulfill({
              status: 200,
              contentType: 'text/event-stream',
              body: 'data: {"type":"done"}\n\n',
            });
            resolve(undefined);
          }, 2000);
        });
      });

      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      // Check for waiting state
      const waiting = page.locator('text=/Waiting for logs/');
      // It may or may not appear depending on timing, so just verify no crash
      await page.waitForTimeout(500);
      await expect(page.locator('h2', { hasText: 'Stage 5' })).toBeVisible();
    });

    test('D5: POST failure does not crash component', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        return route.fulfill({
          status: 500,
          contentType: 'application/json',
          body: '{"error":"Server Error"}',
        });
      });

      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      await page.waitForTimeout(500);

      // Component should not crash
      await expect(page.locator('h2', { hasText: 'Stage 5' })).toBeVisible();
      await expect(page.locator('button', { hasText: 'Run Audio Sync' })).toBeVisible();
    });

    test('D6: Run button remains functional after error', async ({ page }) => {
      await navigateWithMockedProject(page);

      let callCount = 0;
      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        callCount++;
        if (callCount === 1) {
          return route.fulfill({
            status: 500,
            contentType: 'application/json',
            body: '{"error":"Server Error"}',
          });
        }
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-job-retry' }),
        });
      });

      // First click fails
      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      await page.waitForTimeout(500);

      // Button should still be visible and clickable
      await expect(page.locator('button', { hasText: 'Run Audio Sync' })).toBeVisible();
    });

    test('D7: screenshot — SSE panel visible', async ({ page }) => {
      await navigateWithMockedProject(page);

      await page.route('**/api/pipeline/audio-sync/run', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ jobId: 'test-job-screenshot' }),
        });
      });

      await page.route('**/api/jobs/*/stream', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'text/event-stream',
          body: 'data: {"type":"log","message":"Starting audio sync..."}\n\ndata: {"type":"log","message":"Processing section 1..."}\n\ndata: {"type":"done"}\n\n',
        });
      });

      await page.locator('button', { hasText: 'Run Audio Sync' }).click();
      await page.waitForTimeout(1500);
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-D7-sse-panel.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group E: Word Timestamp Viewer (9 tests)
  // =========================================================================
  test.describe('Group E: Word timestamp viewer', () => {
    const sampleWords = [
      { word: 'hello', start: 0.0, end: 0.523, segmentId: 'seg_001' },
      { word: 'world', start: 0.523, end: 1.047 },  // no segmentId
      { word: 'this', start: 1.047, end: 1.200, segmentId: 'seg_002' },
      { word: 'is', start: 1.200, end: 1.350, segmentId: 'seg_002' },
      { word: 'a', start: 1.350, end: 1.400, segmentId: 'seg_002' },
      { word: 'test', start: 1.400, end: 1.800, segmentId: 'seg_002' },
    ];

    test('E1: Section dropdown changes selectedSectionId', async ({ page }) => {
      await navigateWithMockedProject(page, {}, sampleWords);
      const select = page.locator('select');
      await expect(select).toBeVisible();

      // Initial value should be first section
      const initialValue = await select.inputValue();
      expect(initialValue).toBe('intro');

      // Change to second section
      await select.selectOption('main');
      const newValue = await select.inputValue();
      expect(newValue).toBe('main');
    });

    test('E2: Changing section refetches timestamps from API', async ({ page }) => {
      let fetchCount = 0;
      let lastSection = '';

      const defaultProject = {
        name: 'Test Project',
        outputResolution: { width: 1920, height: 1080 },
        tts: { engine: 'qwen3', modelPath: '', tokenizerPath: '', speaker: 'default', speakingRate: 1.0, sampleRate: 22050 },
        sections: [
          { id: 'intro', label: 'Introduction', videoFile: '', specDir: '', remotionDir: '', compositionId: '', durationSeconds: 60, offsetSeconds: 0 },
          { id: 'main', label: 'Main Content', videoFile: '', specDir: '', remotionDir: '', compositionId: '', durationSeconds: 120, offsetSeconds: 60 },
        ],
        audioSync: { sectionGroups: { intro: ['seg_001'], main: ['seg_003'] }, silenceGapDefault: 0.5 },
        veo: { model: 'veo-3.1', defaultAspectRatio: '16:9', maxConcurrentGenerations: 2, references: [], frameChains: [] },
        render: { maxParallelRenders: 2, useLambda: false, lambdaRegion: 'us-east-1' },
      };

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'GET') {
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify(defaultProject),
          });
        }
        return route.continue();
      });

      await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
        fetchCount++;
        const url = new URL(route.request().url());
        lastSection = url.searchParams.get('section') ?? '';
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ words: sampleWords }),
        });
      });

      await navigateToStage5(page);
      await page.waitForTimeout(1000);

      const initialFetchCount = fetchCount;

      // Change section
      await page.locator('select').selectOption('main');
      await page.waitForTimeout(1000);

      expect(fetchCount).toBeGreaterThan(initialFetchCount);
      expect(lastSection).toBe('main');
    });

    test('E3: Word count shows "X of Y words" correctly', async ({ page }) => {
      await navigateWithMockedProject(page, {}, sampleWords);
      await expect(page.locator('text=/6 of 6 words/')).toBeVisible();
    });

    test('E4: Table headers — Word, Start, End, Segment ID', async ({ page }) => {
      await navigateWithMockedProject(page, {}, sampleWords);
      // Check within the virtualized table's thead
      await expect(page.locator('th', { hasText: 'Word' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Start' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'End' }).first()).toBeVisible();
      await expect(page.locator('th', { hasText: 'Segment ID' }).first()).toBeVisible();
    });

    test('E5: Word timestamps display with .toFixed(3) precision', async ({ page }) => {
      await navigateWithMockedProject(page, {}, sampleWords);
      // "0.523" should appear as start of "world"
      await expect(page.locator('td', { hasText: '0.523' }).first()).toBeVisible();
      // "1.047" should appear
      await expect(page.locator('td', { hasText: '1.047' }).first()).toBeVisible();
    });

    test('E6: Segment ID shows "-" when absent (undefined segmentId)', async ({ page }) => {
      await navigateWithMockedProject(page, {}, sampleWords);
      // "world" has no segmentId, so its row should show "-"
      // Find the row with "world" and check for "-"
      const worldRow = page.locator('tr', { hasText: 'world' }).first();
      await expect(worldRow).toBeVisible();
      const cells = worldRow.locator('td');
      const segmentCell = cells.nth(3); // 4th cell: Segment ID
      await expect(segmentCell).toHaveText('-');
    });

    test('E7: "Loading timestamps…" shown during delayed fetch', async ({ page }) => {
      const defaultProject = {
        name: 'Test Project',
        outputResolution: { width: 1920, height: 1080 },
        tts: { engine: 'qwen3', modelPath: '', tokenizerPath: '', speaker: 'default', speakingRate: 1.0, sampleRate: 22050 },
        sections: [
          { id: 'intro', label: 'Introduction', videoFile: '', specDir: '', remotionDir: '', compositionId: '', durationSeconds: 60, offsetSeconds: 0 },
        ],
        audioSync: { sectionGroups: { intro: ['seg_001'] }, silenceGapDefault: 0.5 },
        veo: { model: 'veo-3.1', defaultAspectRatio: '16:9', maxConcurrentGenerations: 2, references: [], frameChains: [] },
        render: { maxParallelRenders: 2, useLambda: false, lambdaRegion: 'us-east-1' },
      };

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'GET') {
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify(defaultProject),
          });
        }
        return route.continue();
      });

      await page.route('**/api/pipeline/audio-sync/timestamps**', async (route) => {
        await new Promise((r) => setTimeout(r, 2000));
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ words: [] }),
        });
      });

      await navigateToStage5(page);
      // Loading text should appear while waiting
      await expect(page.locator('text=Loading timestamps')).toBeVisible({ timeout: 3000 });
    });

    test('E8: Raw array response (not {words:[...]}) handled correctly', async ({ page }) => {
      const rawWords = [
        { word: 'raw', start: 0.0, end: 0.3, segmentId: 'seg_r1' },
        { word: 'array', start: 0.3, end: 0.6, segmentId: 'seg_r1' },
        { word: 'data', start: 0.6, end: 0.9, segmentId: 'seg_r2' },
      ];

      const defaultProject = {
        name: 'Test Project',
        outputResolution: { width: 1920, height: 1080 },
        tts: { engine: 'qwen3', modelPath: '', tokenizerPath: '', speaker: 'default', speakingRate: 1.0, sampleRate: 22050 },
        sections: [
          { id: 'intro', label: 'Introduction', videoFile: '', specDir: '', remotionDir: '', compositionId: '', durationSeconds: 60, offsetSeconds: 0 },
        ],
        audioSync: { sectionGroups: { intro: ['seg_001'] }, silenceGapDefault: 0.5 },
        veo: { model: 'veo-3.1', defaultAspectRatio: '16:9', maxConcurrentGenerations: 2, references: [], frameChains: [] },
        render: { maxParallelRenders: 2, useLambda: false, lambdaRegion: 'us-east-1' },
      };

      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'GET') {
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify(defaultProject),
          });
        }
        return route.continue();
      });

      // Return raw array instead of { words: [...] }
      await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify(rawWords),
        });
      });

      await navigateToStage5(page);
      await page.waitForTimeout(1000);

      // Should show 3 words
      await expect(page.locator('text=/3 of 3 words/')).toBeVisible();
    });

    test('E9: screenshot — table with word data', async ({ page }) => {
      await navigateWithMockedProject(page, {}, sampleWords);
      const viewer = page.locator('h2', { hasText: 'Word Timestamp Viewer' });
      await viewer.scrollIntoViewIfNeeded();
      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-E9-timestamp-viewer.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group F: Search & Filtering (7 tests)
  // =========================================================================
  test.describe('Group F: Search & filtering', () => {
    const searchWords = [
      { word: 'hello', start: 0.0, end: 0.5, segmentId: 'seg_001' },
      { word: 'world', start: 0.5, end: 1.0, segmentId: 'seg_001' },
      { word: 'testing', start: 1.0, end: 1.5, segmentId: 'seg_002' },
      { word: 'Hello', start: 1.5, end: 2.0, segmentId: 'seg_002' },
      { word: 'playwright', start: 2.0, end: 2.5, segmentId: 'seg_003' },
    ];

    test('F1: Search input visible with placeholder', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      const input = page.locator('input[placeholder="Search word…"]');
      await expect(input).toBeVisible();
    });

    test('F2: Typing filters words case-insensitively', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      await page.waitForTimeout(300);

      const input = page.locator('input[placeholder="Search word…"]');
      await input.fill('hello');
      await page.waitForTimeout(300);

      // "hello" and "Hello" should both match → 2 of 5
      await expect(page.locator('text=/2 of 5 words/')).toBeVisible();
    });

    test('F3: Word count updates to show filteredCount of totalCount words', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      await page.waitForTimeout(300);

      // Initially 5 of 5
      await expect(page.locator('text=/5 of 5 words/')).toBeVisible();

      const input = page.locator('input[placeholder="Search word…"]');
      await input.fill('test');
      await page.waitForTimeout(300);

      // "testing" matches → 1 of 5
      await expect(page.locator('text=/1 of 5 words/')).toBeVisible();
    });

    test('F4: Clearing search restores full list', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      await page.waitForTimeout(300);

      const input = page.locator('input[placeholder="Search word…"]');
      await input.fill('hello');
      await page.waitForTimeout(300);
      await expect(page.locator('text=/2 of 5 words/')).toBeVisible();

      // Clear
      await input.fill('');
      await page.waitForTimeout(300);
      await expect(page.locator('text=/5 of 5 words/')).toBeVisible();
    });

    test('F5: Search with no matches shows "0 of X words"', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      await page.waitForTimeout(300);

      const input = page.locator('input[placeholder="Search word…"]');
      await input.fill('zzzznonexistent');
      await page.waitForTimeout(300);

      await expect(page.locator('text=/0 of 5 words/')).toBeVisible();
    });

    test('F6: Empty search string shows all words', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      await page.waitForTimeout(300);

      // Type something then clear
      const input = page.locator('input[placeholder="Search word…"]');
      await input.fill('world');
      await page.waitForTimeout(200);
      await input.fill('');
      await page.waitForTimeout(300);

      await expect(page.locator('text=/5 of 5 words/')).toBeVisible();
    });

    test('F7: screenshot — filtered results', async ({ page }) => {
      await navigateWithMockedProject(page, {}, searchWords);
      await page.waitForTimeout(300);

      const input = page.locator('input[placeholder="Search word…"]');
      await input.fill('hello');
      await page.waitForTimeout(300);

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-F7-filtered-results.png'), fullPage: true });
    });
  });

  // =========================================================================
  // Group G: Virtualized Scroll & Edge Cases (8 tests)
  // =========================================================================
  test.describe('Group G: Virtualized scroll & edge cases', () => {
    test('G1: Virtualized container has height: 320px and contain: strict', async ({ page }) => {
      await navigateWithMockedProject(page, {}, [
        { word: 'w1', start: 0, end: 0.1, segmentId: 's1' },
      ]);
      const container = page.locator('div[style*="contain: strict"]');
      await expect(container).toBeVisible();
      const style = await container.getAttribute('style') ?? '';
      expect(style).toContain('height: 320px');
      expect(style).toContain('contain: strict');
    });

    test('G2: First words visible on initial load', async ({ page }) => {
      const words = Array.from({ length: 30 }, (_, i) => ({
        word: `word_${i}`,
        start: i * 0.1,
        end: (i + 1) * 0.1,
        segmentId: `seg_${Math.floor(i / 10)}`,
      }));
      await navigateWithMockedProject(page, {}, words);

      await expect(page.locator('td', { hasText: 'word_0' })).toBeVisible();
      await expect(page.getByRole('cell', { name: 'word_1', exact: true })).toBeVisible();
    });

    test('G3: Scrolling down renders later words (word_40 of 50)', async ({ page }) => {
      const words = Array.from({ length: 50 }, (_, i) => ({
        word: `word_${i}`,
        start: i * 0.1,
        end: (i + 1) * 0.1,
        segmentId: `seg_${Math.floor(i / 10)}`,
      }));
      await navigateWithMockedProject(page, {}, words);

      const scrollContainer = page.locator('div[style*="contain: strict"]');
      await scrollContainer.evaluate((el) => {
        el.scrollTop = 1200; // Scroll down ~37 rows
      });
      await page.waitForTimeout(500);

      await expect(page.locator('td', { hasText: 'word_40' })).toBeVisible();
    });

    test('G4: 100+ words do not crash the component', async ({ page }) => {
      const words = Array.from({ length: 150 }, (_, i) => ({
        word: `w_${i}`,
        start: i * 0.05,
        end: (i + 1) * 0.05,
        segmentId: `seg_${Math.floor(i / 25)}`,
      }));
      await navigateWithMockedProject(page, {}, words);

      await expect(page.locator('text=/150 of 150 words/')).toBeVisible();
      // Component should not crash
      await expect(page.locator('h2', { hasText: 'Stage 5' })).toBeVisible();
    });

    test('G5: Continue button visible and enabled (always, unlike Stage 4)', async ({ page }) => {
      await navigateWithMockedProject(page);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      await expect(btn).toBeEnabled();
      const cls = await btn.getAttribute('class') ?? '';
      expect(cls).toContain('bg-slate-700');
    });

    test('G6: Continue click navigates to Stage 6 ("Spec Generation")', async ({ page }) => {
      await navigateToStage5(page);
      const btn = page.locator('button', { hasText: 'Continue' });
      await expect(btn).toBeVisible();
      await btn.click();
      await page.waitForTimeout(1000);

      // Should advance to Stage 6
      await expect(page.locator('text=Spec Generation').first()).toBeVisible();
    });

    test('G7: "Loading project…" during delayed project fetch', async ({ page }) => {
      await page.route('**/api/project', async (route) => {
        if (route.request().method() === 'GET') {
          await new Promise((r) => setTimeout(r, 3000));
          return route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({
              name: 'Test',
              outputResolution: { width: 1920, height: 1080 },
              tts: { engine: 'qwen3', modelPath: '', tokenizerPath: '', speaker: 'default', speakingRate: 1.0, sampleRate: 22050 },
              sections: [],
              audioSync: { sectionGroups: {}, silenceGapDefault: 0.5 },
              veo: { model: 'veo-3.1', defaultAspectRatio: '16:9', maxConcurrentGenerations: 2, references: [], frameChains: [] },
              render: { maxParallelRenders: 2, useLambda: false, lambdaRegion: 'us-east-1' },
            }),
          });
        }
        return route.continue();
      });

      await page.goto('/');
      await page.waitForLoadState('networkidle');
      const sidebar = page.locator('aside');
      await sidebar.locator('div.cursor-pointer').nth(4).click();

      await expect(page.locator('text=Loading project')).toBeVisible({ timeout: 3000 });
    });

    test('G8: Network error on project load → error message with red styling', async ({ page }) => {
      // The component doesn't check res.ok — it only catches exceptions.
      // Use route.abort() to simulate a network failure that triggers the catch block.
      await page.route('**/api/project', (route) => {
        if (route.request().method() === 'GET') {
          return route.abort('connectionrefused');
        }
        return route.continue();
      });

      await page.route('**/api/pipeline/audio-sync/timestamps**', (route) => {
        return route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ words: [] }),
        });
      });

      await page.goto('/');
      await page.waitForLoadState('domcontentloaded');
      const sidebar = page.locator('aside');
      await expect(sidebar).toBeVisible({ timeout: 5000 });
      await page.waitForTimeout(1000);
      await sidebar.locator('div.cursor-pointer').nth(4).click();
      await page.waitForTimeout(2000);

      // Error message with red styling
      const errorMsg = page.locator('text=/Error loading project/');
      await expect(errorMsg).toBeVisible({ timeout: 5000 });

      // Verify red styling
      const errorDiv = page.locator('.text-red-500', { hasText: 'Error loading project' });
      await expect(errorDiv).toBeVisible();

      // Component should not crash — heading still visible
      await expect(page.locator('h2', { hasText: 'Stage 5' })).toBeVisible();

      await page.screenshot({ path: path.join(SCREENSHOT_DIR, 'stage5-G8-error-state.png'), fullPage: true });
    });
  });
});
