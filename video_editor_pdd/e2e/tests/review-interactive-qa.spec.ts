import { test, expect, Page, Route } from '@playwright/test';
import type { Annotation, AnnotationAnalysis, Job } from '../../lib/types';

// =============================================================================
// Mock Data
// =============================================================================

const MOCK_PROJECT = {
  name: 'Test Project',
  outputResolution: { width: 1920, height: 1080 },
  tts: { engine: 'qwen3', modelPath: '', tokenizerPath: '', speaker: 'default', speakingRate: 1, sampleRate: 22050 },
  sections: [
    { id: 'cold_open', label: 'Cold Open', videoFile: 'cold_open.mp4', specDir: 'specs/cold_open', remotionDir: 'remotion/cold_open', compositionId: 'ColdOpen', durationSeconds: 30, offsetSeconds: 0 },
  ],
  audioSync: { sectionGroups: {}, silenceGapDefault: 0.3 },
  veo: { model: 'veo-3.1', defaultAspectRatio: '16:9' as const, maxConcurrentGenerations: 3, references: [], frameChains: [] },
  render: { maxParallelRenders: 2, useLambda: false, lambdaRegion: 'us-east-1' },
};

function makeAnnotation(overrides: Partial<Annotation> & { id: string }): Annotation {
  return {
    sectionId: 'cold_open',
    timestamp: 5.3,
    text: 'Test annotation',
    videoFile: 'cold_open.mp4',
    drawingDataUrl: null,
    compositeDataUrl: null,
    analysis: null,
    resolved: false,
    resolveJobId: null,
    fixCommitSha: null,
    inputMethod: 'typed',
    createdAt: '2025-01-01T00:00:00Z',
    ...overrides,
  };
}

const ANALYSIS_CRITICAL_REMOTION: AnnotationAnalysis = {
  severity: 'critical',
  fixType: 'remotion',
  technicalAssessment: 'The text element overflows the safe zone boundary by 15px on the right side.',
  suggestedFixes: ['Reduce font size from 48 to 42', 'Add overflow: hidden to container'],
  confidence: 0.92,
};

const ANALYSIS_MAJOR_TTS: AnnotationAnalysis = {
  severity: 'major',
  fixType: 'tts',
  technicalAssessment: 'Audio narration has timing mismatch with on-screen text appearance.',
  suggestedFixes: ['Re-render TTS with adjusted pacing'],
  confidence: 0.78,
};

const ANALYSIS_MINOR_VEO: AnnotationAnalysis = {
  severity: 'minor',
  fixType: 'veo',
  technicalAssessment: 'Background scene has minor color banding in gradient.',
  suggestedFixes: ['Regenerate with higher quality preset', 'Apply dithering post-process'],
  confidence: 0.65,
};

const ANALYSIS_PASS_NONE: AnnotationAnalysis = {
  severity: 'pass',
  fixType: 'none',
  technicalAssessment: 'Element renders correctly within acceptable tolerances.',
  suggestedFixes: [],
  confidence: 0.95,
};

const MOCK_ANNOTATIONS: Annotation[] = [
  makeAnnotation({
    id: 'ann-1',
    timestamp: 5.3,
    text: 'Text overlaps edge of frame',
    compositeDataUrl: 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
    analysis: ANALYSIS_CRITICAL_REMOTION,
    fixCommitSha: 'abc12345',
  }),
  makeAnnotation({
    id: 'ann-2',
    timestamp: 12.7,
    text: 'Audio timing off during narration',
    analysis: ANALYSIS_MAJOR_TTS,
  }),
  makeAnnotation({
    id: 'ann-3',
    timestamp: 2.1,
    text: 'Background gradient banding',
    compositeDataUrl: 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
    analysis: ANALYSIS_MINOR_VEO,
    resolved: true,
    fixCommitSha: 'def67890',
  }),
  makeAnnotation({
    id: 'ann-4',
    timestamp: 22.0,
    text: 'Scene composition looks correct',
    analysis: ANALYSIS_PASS_NONE,
  }),
  makeAnnotation({
    id: 'ann-5',
    timestamp: 18.5,
    text: 'Possible audio glitch at transition',
    analysis: null,
  }),
];

// unresolvedWithAnalysisCount: ann-1 (critical, unresolved), ann-2 (major, unresolved), ann-4 (pass, unresolved) = 3

const MOCK_JOB_RUNNING: Job = {
  id: 'job-running-1',
  stage: 'render',
  status: 'running',
  progress: 45,
  error: null,
  params: {},
  createdAt: '2025-01-01T00:00:00Z',
  updatedAt: '2025-01-01T00:01:00Z',
};

const MOCK_JOB_ERROR: Job = {
  id: 'job-error-1',
  stage: 'render',
  status: 'error',
  progress: 0,
  error: 'Fix application failed: merge conflict',
  params: {},
  createdAt: '2025-01-01T00:00:00Z',
  updatedAt: '2025-01-01T00:01:00Z',
};

const MOCK_JOB_DONE: Job = {
  id: 'job-done-1',
  stage: 'render',
  status: 'done',
  progress: 100,
  error: null,
  params: {},
  createdAt: '2025-01-01T00:00:00Z',
  updatedAt: '2025-01-01T00:01:00Z',
};

// =============================================================================
// Helpers
// =============================================================================

async function navigateToReview(page: Page) {
  await page.goto('/', { waitUntil: 'load' });
  // Wait for React to render the tab buttons
  const reviewBtn = page.locator('button', { hasText: 'Review' });
  await expect(reviewBtn).toBeVisible({ timeout: 15000 });
  await reviewBtn.click();
  await page.waitForTimeout(500);
}

interface MockOpts {
  annotations?: Annotation[];
  jobs?: Record<string, Job>;
  delayAnnotations?: number;
}

async function navigateWithMockedAnnotations(page: Page, opts: MockOpts = {}) {
  const annotations = opts.annotations ?? MOCK_ANNOTATIONS;
  const jobs = opts.jobs ?? {};

  // Mock project API
  await page.route('**/api/project', (route) => {
    route.fulfill({
      status: 200,
      contentType: 'application/json',
      body: JSON.stringify(MOCK_PROJECT),
    });
  });

  // Mock annotations API — use regex to match with or without query params
  await page.route(/\/api\/annotations(\?.*)?$/, (route: Route) => {
    if (route.request().method() === 'GET') {
      if (opts.delayAnnotations) {
        setTimeout(() => {
          route.fulfill({
            status: 200,
            contentType: 'application/json',
            body: JSON.stringify({ annotations }),
          });
        }, opts.delayAnnotations);
      } else {
        route.fulfill({
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ annotations }),
        });
      }
    } else {
      route.continue();
    }
  });

  // Mock job APIs
  for (const [jobId, job] of Object.entries(jobs)) {
    await page.route(`**/api/jobs/${jobId}`, (route) => {
      if (route.request().url().includes('/stream')) {
        route.continue();
        return;
      }
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(job),
      });
    });
    await page.route(`**/api/jobs/${jobId}/stream`, (route) => {
      route.fulfill({
        status: 200,
        contentType: 'text/event-stream',
        body: '',
      });
    });
  }

  await navigateToReview(page);
  // Wait for annotation panel to load (project config + annotations fetch)
  if (annotations.length > 0) {
    await expect(allCards(page).first()).toBeVisible({ timeout: 15000 });
  } else {
    await page.waitForTimeout(500);
  }
}

/** Get the nth annotation card button (0-indexed), scoped to the annotation list container. */
function nthCard(page: Page, n: number) {
  return page.locator('.flex.flex-col.gap-2 > div button[aria-expanded]').nth(n);
}

/** Get all annotation card buttons, scoped to the annotation list container. */
function allCards(page: Page) {
  return page.locator('.flex.flex-col.gap-2 > div button[aria-expanded]');
}

// =============================================================================
// Group A: Severity & Fix Type Badges (8 tests)
// =============================================================================

test.describe('Review QA — Group A: Severity & Fix Type Badges', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedAnnotations(page);
    // Wait for annotation cards to render
    // Cards loaded via navigateWithMockedAnnotations
  });

  // Sorted by timestamp: ann-3 (2.1), ann-1 (5.3), ann-2 (12.7), ann-5 (18.5), ann-4 (22.0)

  test('A1: critical severity badge shows bg-red-500', async ({ page }) => {
    // ann-1 is index 1 (timestamp 5.3) — has critical severity
    const card = nthCard(page, 1);
    const badge = card.locator('span').filter({ hasText: 'critical' });
    await expect(badge).toBeVisible();
    const hasBgClass = await badge.evaluate((el) => el.classList.contains('bg-red-500'));
    expect(hasBgClass).toBe(true);
  });

  test('A2: major severity badge shows bg-orange-500', async ({ page }) => {
    // ann-2 is index 2 (timestamp 12.7) — has major severity
    const card = nthCard(page, 2);
    const badge = card.locator('span').filter({ hasText: 'major' });
    await expect(badge).toBeVisible();
    const hasBgClass = await badge.evaluate((el) => el.classList.contains('bg-orange-500'));
    expect(hasBgClass).toBe(true);
  });

  test('A3: minor severity badge shows bg-yellow-500', async ({ page }) => {
    // ann-3 is index 0 (timestamp 2.1) — has minor severity
    const card = nthCard(page, 0);
    const badge = card.locator('span').filter({ hasText: 'minor' });
    await expect(badge).toBeVisible();
    const hasBgClass = await badge.evaluate((el) => el.classList.contains('bg-yellow-500'));
    expect(hasBgClass).toBe(true);
  });

  test('A4: pass severity badge shows bg-green-500', async ({ page }) => {
    // ann-4 is index 4 (timestamp 22.0) — has pass severity
    const card = nthCard(page, 4);
    const badge = card.locator('span').filter({ hasText: 'pass' });
    await expect(badge).toBeVisible();
    const hasBgClass = await badge.evaluate((el) => el.classList.contains('bg-green-500'));
    expect(hasBgClass).toBe(true);
  });

  test('A5: Remotion Fix badge visible for remotion fixType', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1: remotion
    const badge = card.locator('span').filter({ hasText: 'Remotion Fix' });
    await expect(badge).toBeVisible();
  });

  test('A6: TTS Re-render badge visible for tts fixType', async ({ page }) => {
    const card = nthCard(page, 2); // ann-2: tts
    const badge = card.locator('span').filter({ hasText: 'TTS Re-render' });
    await expect(badge).toBeVisible();
  });

  test('A7: No Fix badge visible for none fixType', async ({ page }) => {
    const card = nthCard(page, 4); // ann-4: none
    const badge = card.locator('span').filter({ hasText: 'No Fix' });
    await expect(badge).toBeVisible();
  });

  test('A8: Screenshot — severity badges', async ({ page }) => {
    await page.screenshot({ path: 'e2e/screenshots/review-A8-severity-badges.png', fullPage: true });
  });
});

// =============================================================================
// Group B: Timestamps, Thumbnails, Resolved, Sorting (8 tests)
// =============================================================================

test.describe('Review QA — Group B: Timestamps, Thumbnails, Resolved, Sorting', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations
  });

  // Sorted order: ann-3 (2.1), ann-1 (5.3), ann-2 (12.7), ann-5 (18.5), ann-4 (22.0)

  test('B1: timestamps shown in font-mono text-xs text-white/70', async ({ page }) => {
    const card = nthCard(page, 0); // ann-3 timestamp 2.1 → "0:02.1"
    const tsEl = card.locator('.font-mono.text-xs');
    await expect(tsEl).toBeVisible();
    const text = await tsEl.textContent();
    expect(text).toContain('0:02');
  });

  test('B2: annotation with compositeDataUrl shows img thumbnail', async ({ page }) => {
    const card = nthCard(page, 0); // ann-3 has compositeDataUrl
    const img = card.locator('img');
    await expect(img).toBeVisible();
    const hasSizeClasses = await img.evaluate((el) =>
      el.classList.contains('w-20') && el.classList.contains('h-11')
    );
    expect(hasSizeClasses).toBe(true);
  });

  test('B3: annotation without compositeDataUrl shows gray placeholder', async ({ page }) => {
    const card = nthCard(page, 2); // ann-2 has no compositeDataUrl
    // Should NOT have an img
    await expect(card.locator('img')).toHaveCount(0);
    // Should have a gray placeholder div (h-11 w-20 bg-white/5)
    const placeholder = card.locator('div.h-11.w-20');
    await expect(placeholder).toBeVisible();
    const hasBgClass = await placeholder.evaluate((el) => el.classList.contains('bg-white/5'));
    expect(hasBgClass).toBe(true);
  });

  test('B4: resolved annotation shows ✓ Resolved badge', async ({ page }) => {
    const card = nthCard(page, 0); // ann-3 is resolved
    const resolvedBadge = card.locator('span').filter({ hasText: '✓ Resolved' });
    await expect(resolvedBadge).toBeVisible();
    const hasBgClass = await resolvedBadge.evaluate((el) =>
      el.classList.contains('bg-green-500/20')
    );
    expect(hasBgClass).toBe(true);
  });

  test('B5: resolved card has green border and bg', async ({ page }) => {
    const card = nthCard(page, 0); // ann-3 resolved
    // The card's parent div (the one with border classes)
    const cardDiv = card.locator('..'); // parent
    const hasGreenBorder = await cardDiv.evaluate((el) =>
      el.classList.contains('border-green-500/30') && el.classList.contains('bg-green-500/5')
    );
    expect(hasGreenBorder).toBe(true);
  });

  test('B6: unresolved card has white/10 border and white/5 bg', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1 unresolved
    const cardDiv = card.locator('..');
    const hasDefaultBorder = await cardDiv.evaluate((el) =>
      el.classList.contains('border-white/10') && el.classList.contains('bg-white/5')
    );
    expect(hasDefaultBorder).toBe(true);
  });

  test('B7: annotations sorted by timestamp ascending', async ({ page }) => {
    const cards = allCards(page);
    const count = await cards.count();
    expect(count).toBe(5);

    // Extract timestamp text from each card to verify order
    const timestamps: string[] = [];
    for (let i = 0; i < count; i++) {
      const tsEl = cards.nth(i).locator('.font-mono.text-xs');
      const text = await tsEl.textContent();
      timestamps.push(text ?? '');
    }
    // ann-3=2.1, ann-1=5.3, ann-2=12.7, ann-5=18.5, ann-4=22.0
    expect(timestamps[0]).toContain('0:02');
    expect(timestamps[1]).toContain('0:05');
    expect(timestamps[2]).toContain('0:12');
    expect(timestamps[3]).toContain('0:18');
    expect(timestamps[4]).toContain('0:22');
  });

  test('B8: Screenshot — resolved states', async ({ page }) => {
    await page.screenshot({ path: 'e2e/screenshots/review-B8-resolved-states.png', fullPage: true });
  });
});

// =============================================================================
// Group C: Expanded Details (9 tests)
// =============================================================================

test.describe('Review QA — Group C: Expanded Details', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations
  });

  test('C1: click card toggles expanded via aria-expanded', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1
    // Initially collapsed
    await expect(card).toHaveAttribute('aria-expanded', 'false');
    await card.click();
    await page.waitForTimeout(300);
    await expect(card).toHaveAttribute('aria-expanded', 'true');
    // Click again to collapse
    await card.click();
    await page.waitForTimeout(300);
    await expect(card).toHaveAttribute('aria-expanded', 'false');
  });

  test('C2: expanded shows technical assessment text', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1 critical/remotion
    await card.click();
    await page.waitForTimeout(300);

    const assessmentLabel = card.locator('..').locator('text=Technical assessment');
    await expect(assessmentLabel).toBeVisible();

    const assessmentText = card.locator('..').locator('.text-xs.text-white\\/85').first();
    await expect(assessmentText).toContainText('text element overflows');
  });

  test('C3: expanded shows suggested fixes as li items', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1: has 2 suggested fixes
    await card.click();
    await page.waitForTimeout(300);

    const liItems = card.locator('..').locator('li');
    await expect(liItems).toHaveCount(2);
    await expect(liItems.first()).toContainText('Reduce font size');
    await expect(liItems.nth(1)).toContainText('overflow: hidden');
  });

  test('C4: View Diff button visible when fixCommitSha exists (bg-blue-500/20)', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1 has fixCommitSha
    await card.click();
    await page.waitForTimeout(300);

    const viewDiffBtn = card.locator('..').locator('button', { hasText: 'View Diff' });
    await expect(viewDiffBtn).toBeVisible();
    const hasBgClass = await viewDiffBtn.evaluate((el) =>
      el.classList.contains('bg-blue-500/20')
    );
    expect(hasBgClass).toBe(true);
  });

  test('C5: Revert Fix button visible when fixCommitSha exists (bg-red-500/20)', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1 has fixCommitSha
    await card.click();
    await page.waitForTimeout(300);

    const revertBtn = card.locator('..').locator('button', { hasText: 'Revert Fix' });
    await expect(revertBtn).toBeVisible();
    const hasBgClass = await revertBtn.evaluate((el) =>
      el.classList.contains('bg-red-500/20')
    );
    expect(hasBgClass).toBe(true);
  });

  test('C6: View Diff + Revert Fix NOT visible when fixCommitSha is null', async ({ page }) => {
    const card = nthCard(page, 2); // ann-2 has no fixCommitSha
    await card.click();
    await page.waitForTimeout(300);

    const viewDiffBtn = card.locator('..').locator('button', { hasText: 'View Diff' });
    const revertBtn = card.locator('..').locator('button', { hasText: 'Revert Fix' });
    await expect(viewDiffBtn).toHaveCount(0);
    await expect(revertBtn).toHaveCount(0);
  });

  test('C7: Mark Resolved visible for unresolved, absent for resolved', async ({ page }) => {
    // ann-1 unresolved (index 1) — should have Mark Resolved
    const unresolvedCard = nthCard(page, 1);
    await unresolvedCard.click();
    await page.waitForTimeout(300);
    const markBtn = unresolvedCard.locator('..').locator('button', { hasText: 'Mark Resolved' });
    await expect(markBtn).toBeVisible();

    // collapse it
    await unresolvedCard.click();
    await page.waitForTimeout(300);

    // ann-3 resolved (index 0) — should NOT have Mark Resolved
    const resolvedCard = nthCard(page, 0);
    await resolvedCard.click();
    await page.waitForTimeout(300);
    const markBtnResolved = resolvedCard.locator('..').locator('button', { hasText: 'Mark Resolved' });
    await expect(markBtnResolved).toHaveCount(0);
  });

  test('C8: annotation with null analysis shows "No analysis available." and "None."', async ({ page }) => {
    const card = nthCard(page, 3); // ann-5 has null analysis (index 3, timestamp 18.5)
    await card.click();
    await page.waitForTimeout(300);

    const parent = card.locator('..');
    await expect(parent.locator('text=No analysis available.')).toBeVisible();
    await expect(parent.locator('text=None.')).toBeVisible();
  });

  test('C9: Screenshot — expanded details', async ({ page }) => {
    // Expand ann-1
    const card = nthCard(page, 1);
    await card.click();
    await page.waitForTimeout(300);
    await page.screenshot({ path: 'e2e/screenshots/review-C9-expanded-details.png', fullPage: true });
  });
});

// =============================================================================
// Group D: View Diff, Revert, Mark Resolved, Retry (8 tests)
// =============================================================================

test.describe('Review QA — Group D: View Diff, Revert, Mark Resolved, Retry', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations
  });

  test('D1: View Diff fetches diff and displays in <pre>', async ({ page }) => {
    // Mock diff API
    await page.route('**/api/annotations/ann-1/diff', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ diff: '--- a/src/comp.tsx\n+++ b/src/comp.tsx\n@@ -10,3 +10,3 @@\n-  fontSize: 48,\n+  fontSize: 42,' }),
      });
    });

    const card = nthCard(page, 1); // ann-1
    await card.click();
    await page.waitForTimeout(300);

    const viewDiffBtn = card.locator('..').locator('button', { hasText: 'View Diff' });
    await viewDiffBtn.click();
    await page.waitForTimeout(500);

    const diffPre = card.locator('..').locator('pre');
    await expect(diffPre).toBeVisible();
    await expect(diffPre).toContainText('fontSize: 42');
  });

  test('D2: View Diff toggles to "Hide Diff" on second click', async ({ page }) => {
    await page.route('**/api/annotations/ann-1/diff', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ diff: 'some diff content' }),
      });
    });

    const card = nthCard(page, 1);
    await card.click();
    await page.waitForTimeout(300);

    const parent = card.locator('..');
    const viewDiffBtn = parent.locator('button', { hasText: 'View Diff' });
    await viewDiffBtn.click();
    await page.waitForTimeout(500);

    // Now should say "Hide Diff"
    const hideDiffBtn = parent.locator('button', { hasText: 'Hide Diff' });
    await expect(hideDiffBtn).toBeVisible();

    // Click again to hide
    await hideDiffBtn.click();
    await page.waitForTimeout(300);

    // Should be back to "View Diff"
    await expect(parent.locator('button', { hasText: 'View Diff' })).toBeVisible();
    await expect(parent.locator('pre')).toHaveCount(0);
  });

  test('D3: View Diff shows "Loading..." while fetch in flight', async ({ page }) => {
    // Mock with a delay
    await page.route('**/api/annotations/ann-1/diff', async (route) => {
      await new Promise((r) => setTimeout(r, 2000));
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ diff: 'delayed diff' }),
      });
    });

    const card = nthCard(page, 1);
    await card.click();
    await page.waitForTimeout(300);

    const parent = card.locator('..');
    const viewDiffBtn = parent.locator('button', { hasText: 'View Diff' });
    await viewDiffBtn.click();

    // Should immediately show "Loading..."
    const loadingBtn = parent.locator('button', { hasText: 'Loading...' });
    await expect(loadingBtn).toBeVisible();
    await expect(loadingBtn).toBeDisabled();
  });

  test('D4: Revert Fix POSTs to /api/annotations/{id}/revert', async ({ page }) => {
    let revertCalled = false;
    await page.route('**/api/annotations/ann-1/revert', (route) => {
      revertCalled = true;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ success: true }),
      });
    });

    // Accept the confirm dialog
    page.on('dialog', (dialog) => dialog.accept());

    const card = nthCard(page, 1);
    await card.click();
    await page.waitForTimeout(300);

    const revertBtn = card.locator('..').locator('button', { hasText: 'Revert Fix' });
    await revertBtn.click();
    await page.waitForTimeout(500);

    expect(revertCalled).toBe(true);
  });

  test('D5: Mark Resolved toggles card to resolved state', async ({ page }) => {
    const card = nthCard(page, 1); // ann-1 unresolved
    await card.click();
    await page.waitForTimeout(300);

    // Initially no ✓ Resolved badge
    await expect(card.locator('span').filter({ hasText: '✓ Resolved' })).toHaveCount(0);

    const markBtn = card.locator('..').locator('button', { hasText: 'Mark Resolved' });
    await markBtn.click();
    await page.waitForTimeout(300);

    // Now should show ✓ Resolved
    await expect(card.locator('span').filter({ hasText: '✓ Resolved' })).toBeVisible();
  });

  test('D6: Mark Resolved decrements Apply N Fixes count', async ({ page }) => {
    // Initially should be "Apply 3 Fixes" (ann-1, ann-2, ann-4 are unresolved with analysis)
    const applyBtn = page.locator('button', { hasText: /Apply \d+ Fixes/ });
    await expect(applyBtn).toContainText('Apply 3 Fixes');

    // Expand ann-1 and mark resolved
    const card = nthCard(page, 1);
    await card.click();
    await page.waitForTimeout(300);

    const markBtn = card.locator('..').locator('button', { hasText: 'Mark Resolved' });
    await markBtn.click();
    await page.waitForTimeout(300);

    // Now should be "Apply 2 Fixes"
    await expect(applyBtn).toContainText('Apply 2 Fixes');
  });

  test('D7: Retry button visible when resolveJobId has error status job', async ({ page }) => {
    test.setTimeout(60000); // Extra time: navigates twice (beforeEach + here)
    const annotationsWithErrorJob = [
      makeAnnotation({
        id: 'ann-err',
        timestamp: 5.0,
        text: 'Failed fix annotation',
        analysis: ANALYSIS_CRITICAL_REMOTION,
        resolveJobId: 'job-error-1',
      }),
    ];

    await navigateWithMockedAnnotations(page, {
      annotations: annotationsWithErrorJob,
      jobs: { 'job-error-1': MOCK_JOB_ERROR },
    });
    // Cards loaded via navigateWithMockedAnnotations

    const card = nthCard(page, 0);
    await card.click();
    await page.waitForTimeout(1000); // Wait for job fetch

    const retryBtn = card.locator('..').locator('button', { hasText: 'Retry' });
    await expect(retryBtn).toBeVisible();
  });

  test('D8: Screenshot — diff view', async ({ page }) => {
    await page.route('**/api/annotations/ann-1/diff', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ diff: '--- a/src/comp.tsx\n+++ b/src/comp.tsx\n-  fontSize: 48,\n+  fontSize: 42,' }),
      });
    });

    const card = nthCard(page, 1);
    await card.click();
    await page.waitForTimeout(300);
    const viewDiffBtn = card.locator('..').locator('button', { hasText: 'View Diff' });
    await viewDiffBtn.click();
    await page.waitForTimeout(500);

    await page.screenshot({ path: 'e2e/screenshots/review-D8-diff-view.png', fullPage: true });
  });
});

// =============================================================================
// Group E: Apply Fixes & FixPreviewPanel (9 tests)
// =============================================================================

test.describe('Review QA — Group E: Apply Fixes & FixPreviewPanel', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations
  });

  test('E1: Apply Fixes button shows correct unresolved analyzed count', async ({ page }) => {
    const applyBtn = page.locator('button', { hasText: /Apply \d+ Fixes/ });
    await expect(applyBtn).toContainText('Apply 3 Fixes');
  });

  test('E2: Apply Fixes disabled when count is 0', async ({ page }) => {
    test.setTimeout(60000); // Extra time: navigates twice (beforeEach + here)
    // All resolved annotations
    const allResolved = MOCK_ANNOTATIONS.map((a) => ({ ...a, resolved: true }));
    await navigateWithMockedAnnotations(page, { annotations: allResolved });
    // Cards loaded via navigateWithMockedAnnotations

    const applyBtn = page.locator('button', { hasText: /Apply 0 Fixes/ });
    await expect(applyBtn).toBeDisabled();
  });

  test('E3: click Apply Fixes opens FixPreviewPanel', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', async (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          previews: [
            { annotationId: 'ann-1', fixType: 'remotion', preview: 'Adjust font size', diff: null, confidence: 0.9 },
          ],
        }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('text=Fix Preview')).toBeVisible();
  });

  test('E4: FixPreviewPanel shows "Generating previews..." spinner while loading', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', async (route) => {
      await new Promise((r) => setTimeout(r, 5000));
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ previews: [] }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(300);

    await expect(page.locator('text=Generating previews...')).toBeVisible();
  });

  test('E5: FixPreviewPanel shows error state on API 500', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 500,
        contentType: 'application/json',
        body: JSON.stringify({ error: 'Internal Server Error' }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(1000);

    // Error state message
    const errorEl = page.locator('.text-red-200');
    await expect(errorEl).toBeVisible();
    await expect(errorEl).toContainText('Preview failed');
  });

  test('E6: FixPreviewPanel shows "No fixes to preview." when empty', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ previews: [] }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    await expect(page.locator('text=No fixes to preview.')).toBeVisible();
  });

  test('E7: checkbox toggle updates "N of M fixes selected" count', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          previews: [
            { annotationId: 'ann-1', fixType: 'remotion', preview: 'Fix 1', diff: null, confidence: 0.9 },
            { annotationId: 'ann-2', fixType: 'tts', preview: 'Fix 2', diff: null, confidence: 0.8 },
          ],
        }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    // Initially "2 of 2 fixes selected"
    await expect(page.locator('text=2 of 2 fixes selected')).toBeVisible();

    // Uncheck first checkbox
    const checkboxes = page.locator('input[type="checkbox"]');
    await checkboxes.first().uncheck();
    await page.waitForTimeout(200);

    await expect(page.locator('text=1 of 2 fixes selected')).toBeVisible();
  });

  test('E8: Apply button POSTs to resolve-batch with selected annotationIds', async ({ page }) => {
    let postedIds: string[] = [];
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          previews: [
            { annotationId: 'ann-1', fixType: 'remotion', preview: 'Fix 1', diff: null, confidence: 0.9 },
            { annotationId: 'ann-2', fixType: 'tts', preview: 'Fix 2', diff: null, confidence: 0.8 },
          ],
        }),
      });
    });

    await page.route('**/api/sections/cold_open/resolve-batch', async (route) => {
      const body = route.request().postDataJSON();
      postedIds = body.annotationIds;
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'batch-job-1' }),
      });
    });

    // Mock job stream for batch job
    await page.route('**/api/jobs/batch-job-1/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });
    await page.route('**/api/jobs/batch-job-1', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(MOCK_JOB_RUNNING),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    // Uncheck ann-2
    const checkboxes = page.locator('input[type="checkbox"]');
    await checkboxes.nth(1).uncheck();
    await page.waitForTimeout(200);

    // Click the green "Apply 1 Fixes" button
    const applyFixesBtn = page.locator('button.bg-green-600', { hasText: /Apply \d+ Fixes/ });
    await applyFixesBtn.click();
    await page.waitForTimeout(500);

    expect(postedIds).toEqual(['ann-1']);
  });

  test('E9: Screenshot — fix preview panel', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          previews: [
            { annotationId: 'ann-1', fixType: 'remotion', preview: 'Adjust font size to 42', diff: '--- a\n+++ b\n-48\n+42', confidence: 0.92 },
            { annotationId: 'ann-2', fixType: 'tts', preview: 'Re-render TTS audio', diff: null, confidence: 0.78 },
          ],
        }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    await page.screenshot({ path: 'e2e/screenshots/review-E9-fix-preview.png', fullPage: true });
  });
});

// =============================================================================
// Group F: SseLogPanel Batch Streaming (7 tests)
// =============================================================================

test.describe('Review QA — Group F: SseLogPanel Batch Streaming', () => {
  async function triggerBatchJob(page: Page) {
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          previews: [
            { annotationId: 'ann-1', fixType: 'remotion', preview: 'Fix 1', diff: null, confidence: 0.9 },
          ],
        }),
      });
    });

    await page.route('**/api/sections/cold_open/resolve-batch', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'batch-job-sse' }),
      });
    });

    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    const applyFixesBtn = page.locator('button.bg-green-600', { hasText: /Apply/ });
    await applyFixesBtn.click();
    await page.waitForTimeout(300);
  }

  test('F1: SseLogPanel shows "Waiting for logs…" initially', async ({ page }) => {
    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      // Never fulfill — keep connection pending
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_RUNNING, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);

    await expect(page.locator('text=Waiting for logs…')).toBeVisible();
  });

  test('F2: SseLogPanel displays log lines from SSE messages', async ({ page }) => {
    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      const body = [
        'data: {"message":"Starting fix for ann-1..."}\n\n',
        'data: {"message":"Applying remotion patch..."}\n\n',
      ].join('');
      route.fulfill({ status: 200, contentType: 'text/event-stream', body });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_RUNNING, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);
    await page.waitForTimeout(1000);

    await expect(page.locator('text=Starting fix for ann-1...')).toBeVisible();
    await expect(page.locator('text=Applying remotion patch...')).toBeVisible();
  });

  test('F3: SseLogPanel shows green "✓ Completed" on done event', async ({ page }) => {
    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      const body = 'data: {"message":"All done"}\n\nevent: done\ndata: {}\n\n';
      route.fulfill({ status: 200, contentType: 'text/event-stream', body });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_DONE, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);
    await page.waitForTimeout(1000);

    const completedEl = page.locator('.text-green-400');
    await expect(completedEl).toContainText('✓ Completed');
  });

  test('F4: SseLogPanel shows red "✕ Error:" on error event', async ({ page }) => {
    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      const body = 'event: error\ndata: {"message":"Merge conflict"}\n\n';
      route.fulfill({ status: 200, contentType: 'text/event-stream', body });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_ERROR, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);
    await page.waitForTimeout(1000);

    const errorEl = page.locator('.text-red-400');
    await expect(errorEl).toContainText('✕ Error:');
  });

  test('F5: SseLogPanel auto-scrolls to bottom on new log lines', async ({ page }) => {
    // Generate many log lines to force scroll
    const lines = Array.from({ length: 30 }, (_, i) =>
      `data: {"message":"Processing step ${i + 1}..."}\n\n`
    ).join('');

    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: lines });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_RUNNING, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);
    await page.waitForTimeout(1500);

    // Check that the log container is scrolled to bottom
    const logContainer = page.locator('.overflow-y-auto.max-h-64.font-mono');
    const isScrolledToBottom = await logContainer.evaluate((el) => {
      return Math.abs(el.scrollHeight - el.scrollTop - el.clientHeight) < 10;
    });
    expect(isScrolledToBottom).toBe(true);
  });

  test('F6: batch job section shows jobId label', async ({ page }) => {
    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_RUNNING, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);
    await page.waitForTimeout(500);

    await expect(page.locator('text=jobId: batch-job-sse')).toBeVisible();
  });

  test('F7: Screenshot — SSE logs', async ({ page }) => {
    const lines = Array.from({ length: 5 }, (_, i) =>
      `data: {"message":"Processing step ${i + 1}..."}\n\n`
    ).join('');

    await page.route('**/api/jobs/batch-job-sse/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: lines + 'event: done\ndata: {}\n\n' });
    });
    await page.route('**/api/jobs/batch-job-sse', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_DONE, id: 'batch-job-sse' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    await triggerBatchJob(page);
    await page.waitForTimeout(1000);

    await page.screenshot({ path: 'e2e/screenshots/review-F7-sse-logs.png', fullPage: true });
  });
});

// =============================================================================
// Group G: Recording Mode UI & Progress Bar Markers (8 tests)
// =============================================================================

test.describe('Review QA — Group G: Recording Mode & Progress Bar Markers', () => {
  test.beforeEach(async ({ page }) => {
    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations
  });

  test('G1: status indicator shows "Review" in default mode', async ({ page }) => {
    const statusBadge = page.locator('.bg-black\\/60').first();
    await expect(statusBadge).toContainText('Review');
  });

  test('G2: pressing Space changes status to "Recording"', async ({ page }) => {
    await page.keyboard.press('Space');
    await page.waitForTimeout(500);

    const statusBadge = page.locator('.bg-black\\/60').first();
    await expect(statusBadge).toContainText('Recording');

    // Cleanup: stop recording
    await page.keyboard.press('Space');
  });

  test('G3: recording mode shows red pulsing dot', async ({ page }) => {
    await page.keyboard.press('Space');
    await page.waitForTimeout(500);

    const redDot = page.locator('.bg-red-500.animate-pulse');
    await expect(redDot).toBeVisible();

    await page.keyboard.press('Space');
  });

  test('G4: recording mode shows transcript overlay', async ({ page }) => {
    await page.keyboard.press('Space');
    await page.waitForTimeout(500);

    const transcriptOverlay = page.locator('text=Transcript:');
    await expect(transcriptOverlay).toBeVisible();

    await page.keyboard.press('Space');
  });

  test('G5: canvas pointer-events: none in review, auto in recording', async ({ page }) => {
    const canvas = page.locator('canvas');

    // Default: pointer-events none
    const peDefault = await canvas.evaluate((el) => el.style.pointerEvents);
    expect(peDefault).toBe('none');

    // Recording mode: pointer-events auto
    await page.keyboard.press('Space');
    await page.waitForTimeout(500);

    const peRecording = await canvas.evaluate((el) => el.style.pointerEvents);
    expect(peRecording).toBe('auto');

    await page.keyboard.press('Space');
  });

  test('G6: yellow annotation markers on progress bar', async ({ page }) => {
    const markers = page.locator('button.bg-yellow-400');
    await expect(markers).toHaveCount(5); // 5 annotations
  });

  test('G7: clicking annotation marker seeks video', async ({ page }) => {
    // ann-3 is at timestamp 2.1 — first marker (sorted by timestamp)
    const markers = page.locator('button.bg-yellow-400');
    const firstMarker = markers.first();

    // Verify aria-label format
    const ariaLabel = await firstMarker.getAttribute('aria-label');
    expect(ariaLabel).toContain('annotation at');
    expect(ariaLabel).toContain('seconds');

    // Click the marker
    await firstMarker.click();
    await page.waitForTimeout(300);

    // Video should have seeked (verify no crash)
    const video = page.locator('video');
    await expect(video).toBeAttached();
  });

  test('G8: Screenshot — recording mode', async ({ page }) => {
    await page.keyboard.press('Space');
    await page.waitForTimeout(500);

    await page.screenshot({ path: 'e2e/screenshots/review-G8-recording-mode.png', fullPage: true });

    await page.keyboard.press('Space');
  });
});

// =============================================================================
// Group H: Loading State, Edge Cases, Inline Progress (7 tests)
// =============================================================================

test.describe('Review QA — Group H: Loading State & Edge Cases', () => {
  test('H1: "Loading annotations..." visible during slow fetch', async ({ page }) => {
    await page.route('**/api/project', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(MOCK_PROJECT),
      });
    });

    // Delay annotations response
    await page.route('**/api/annotations?*', async (route) => {
      await new Promise((r) => setTimeout(r, 3000));
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ annotations: MOCK_ANNOTATIONS }),
      });
    });

    await navigateToReview(page);

    await expect(page.locator('text=Loading annotations...')).toBeVisible();
  });

  test('H2: loading text disappears after annotations load', async ({ page }) => {
    await page.route('**/api/project', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify(MOCK_PROJECT),
      });
    });

    let resolveRoute: ((route: Route) => void) | null = null;
    await page.route('**/api/annotations?*', (route) => {
      if (route.request().method() === 'GET') {
        resolveRoute = route.fulfill.bind(route, {
          status: 200,
          contentType: 'application/json',
          body: JSON.stringify({ annotations: MOCK_ANNOTATIONS }),
        });
        // Don't fulfill yet — wait for assertion
      } else {
        route.continue();
      }
    });

    await navigateToReview(page);
    await expect(page.locator('text=Loading annotations...')).toBeVisible();

    // Now fulfill the request
    if (resolveRoute) resolveRoute(null as any);
    await page.waitForTimeout(500);

    await expect(page.locator('text=Loading annotations...')).not.toBeVisible();
  });

  test('H3: empty annotations shows "No annotations yet."', async ({ page }) => {
    await navigateWithMockedAnnotations(page, { annotations: [] });
    await page.waitForTimeout(500);

    await expect(page.locator('text=No annotations yet.')).toBeVisible();
  });

  test('H4: inline progress spinner for annotation with running resolveJobId', async ({ page }) => {
    const runningAnnotations = [
      makeAnnotation({
        id: 'ann-running',
        timestamp: 5.0,
        text: 'Running fix annotation',
        analysis: ANALYSIS_CRITICAL_REMOTION,
        resolveJobId: 'job-running-1',
      }),
    ];

    await navigateWithMockedAnnotations(page, {
      annotations: runningAnnotations,
      jobs: { 'job-running-1': MOCK_JOB_RUNNING },
    });
    // Cards loaded via navigateWithMockedAnnotations
    await page.waitForTimeout(1500); // Wait for job fetch

    // Should show spinner with status
    const spinner = page.locator('[aria-label="Loading"]');
    await expect(spinner.first()).toBeVisible();
  });

  test('H5: no spinner for annotation with terminal (error) job', async ({ page }) => {
    const errorAnnotations = [
      makeAnnotation({
        id: 'ann-err',
        timestamp: 5.0,
        text: 'Failed fix',
        analysis: ANALYSIS_CRITICAL_REMOTION,
        resolveJobId: 'job-error-1',
      }),
    ];

    await navigateWithMockedAnnotations(page, {
      annotations: errorAnnotations,
      jobs: { 'job-error-1': MOCK_JOB_ERROR },
    });
    // Cards loaded via navigateWithMockedAnnotations
    await page.waitForTimeout(1500); // Wait for job fetch

    // The inline progress (with spinner) should NOT be visible because job is terminal
    const card = nthCard(page, 0);
    const inlineProgress = card.locator('[aria-label="Loading"]');
    await expect(inlineProgress).toHaveCount(0);
  });

  test('H6: Apply Fixes button disabled after batch job starts', async ({ page }) => {
    await page.route('**/api/sections/cold_open/preview-fixes', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({
          previews: [
            { annotationId: 'ann-1', fixType: 'remotion', preview: 'Fix 1', diff: null, confidence: 0.9 },
          ],
        }),
      });
    });

    await page.route('**/api/sections/cold_open/resolve-batch', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ jobId: 'batch-job-h6' }),
      });
    });

    await page.route('**/api/jobs/batch-job-h6/stream', (route) => {
      route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    });
    await page.route('**/api/jobs/batch-job-h6', (route) => {
      route.fulfill({
        status: 200,
        contentType: 'application/json',
        body: JSON.stringify({ ...MOCK_JOB_RUNNING, id: 'batch-job-h6' }),
      });
    });

    await navigateWithMockedAnnotations(page);
    // Cards loaded via navigateWithMockedAnnotations

    // Open preview and apply
    const applyBtn = page.locator('button', { hasText: /Apply 3 Fixes/ });
    await applyBtn.click();
    await page.waitForTimeout(500);

    const applyFixesBtn = page.locator('button.bg-green-600', { hasText: /Apply/ });
    await applyFixesBtn.click();
    await page.waitForTimeout(500);

    // Now the top-level Apply button should be disabled
    await expect(applyBtn).toBeDisabled();
  });

  test('H7: Screenshot — loading & progress', async ({ page }) => {
    const runningAnnotations = [
      makeAnnotation({
        id: 'ann-running',
        timestamp: 5.0,
        text: 'Running fix annotation',
        analysis: ANALYSIS_CRITICAL_REMOTION,
        resolveJobId: 'job-running-1',
      }),
      makeAnnotation({
        id: 'ann-normal',
        timestamp: 10.0,
        text: 'Normal annotation',
        analysis: ANALYSIS_MAJOR_TTS,
      }),
    ];

    await navigateWithMockedAnnotations(page, {
      annotations: runningAnnotations,
      jobs: { 'job-running-1': MOCK_JOB_RUNNING },
    });
    // Cards loaded via navigateWithMockedAnnotations
    await page.waitForTimeout(1500);

    await page.screenshot({ path: 'e2e/screenshots/review-H7-loading-progress.png', fullPage: true });
  });
});
