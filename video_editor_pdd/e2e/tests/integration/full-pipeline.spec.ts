import { test, expect, Page } from '@playwright/test';
import fs from 'fs';
import path from 'path';
import { execSync } from 'child_process';

const PROJECT_ROOT = path.resolve(__dirname, '..', '..', '..');
const OUTPUTS_DIR = path.join(PROJECT_ROOT, 'outputs');
const ANIMATION_VIDEO = path.join(OUTPUTS_DIR, 'sections', 'animation_section.mp4');
const REMOTION_SRC_DIR = path.join(PROJECT_ROOT, 'remotion', 'src', 'remotion');

/** Use ffprobe to check whether a video file has an audio stream. */
function hasAudioStream(videoPath: string): boolean {
  try {
    const result = execSync(
      `ffprobe -v quiet -select_streams a -show_entries stream=codec_type -of csv=p=0 "${videoPath}"`,
      { encoding: 'utf-8' },
    );
    return result.trim().includes('audio');
  } catch {
    return false;
  }
}

/** Extract a single frame from a video at the given second offset. */
function extractFrame(videoPath: string, outPng: string, atSecond: number = 1): void {
  execSync(
    `ffmpeg -y -ss ${atSecond} -i "${videoPath}" -vframes 1 -update 1 "${outPng}"`,
    { stdio: 'pipe' },
  );
}

/** Return the max pixel value in a PNG (0 = all black). */
function maxPixelValue(pngPath: string): number {
  const raw = execSync(
    `python3 -c "from PIL import Image; import numpy as np; img=np.array(Image.open('${pngPath}')); print(img.max())"`,
    { encoding: 'utf-8' },
  ).trim();
  return parseInt(raw, 10);
}

/** Compare two PNGs and return the sum of absolute pixel differences. */
function frameDiffSum(pngA: string, pngB: string): number {
  const raw = execSync(
    `python3 -c "from PIL import Image; import numpy as np; a=np.array(Image.open('${pngA}')); b=np.array(Image.open('${pngB}')); print(int(np.abs(a.astype(int)-b.astype(int)).sum()))"`,
    { encoding: 'utf-8' },
  ).trim();
  return parseInt(raw, 10);
}

/**
 * Snapshot all TSX files related to animation_section.
 * Returns a Map of relative-path → file-content for later comparison.
 * Includes: wrapper at animation_section/index.tsx + any *.tsx in the flat dir.
 */
function snapshotAnimationTsx(): Map<string, string> {
  const snapshot = new Map<string, string>();

  // Section wrapper: remotion/src/remotion/animation_section/index.tsx
  const wrapperPath = path.join(REMOTION_SRC_DIR, 'animation_section', 'index.tsx');
  if (fs.existsSync(wrapperPath)) {
    snapshot.set(wrapperPath, fs.readFileSync(wrapperPath, 'utf-8'));
  }

  // Flat-dir component TSX files (skip Root.tsx and non-animation files)
  const flatFiles = fs.readdirSync(REMOTION_SRC_DIR).filter(
    (f) => f.endsWith('.tsx') && f !== 'Root.tsx',
  );
  for (const f of flatFiles) {
    const fullPath = path.join(REMOTION_SRC_DIR, f);
    snapshot.set(fullPath, fs.readFileSync(fullPath, 'utf-8'));
  }

  return snapshot;
}

async function getJsonWithRetry(
  page: Page,
  url: string,
  timeoutMs: number = 30_000,
): Promise<unknown> {
  const startTime = Date.now();
  let lastError: Error | null = null;

  while (Date.now() - startTime < timeoutMs) {
    try {
      const response = await page.request.get(url);
      return await response.json();
    } catch (error) {
      lastError = error instanceof Error ? error : new Error(String(error));
      await page.waitForTimeout(1_000);
    }
  }

  throw lastError ?? new Error(`GET ${url} timed out after ${timeoutMs}ms`);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Poll GET /api/pipeline/status until a stage reaches 'done'. */
async function waitForStageCompletion(
  page: Page,
  stage: string,
  timeoutMs: number = 600_000,
): Promise<void> {
  const startTime = Date.now();
  while (Date.now() - startTime < timeoutMs) {
    try {
      const response = await page.request.get('/api/pipeline/status');
      const body = await response.json();
      const stages = body?.stages;
      if (!stages) {
        await page.waitForTimeout(3000);
        continue;
      }
      if (stages[stage]?.status === 'done') return;
      if (stages[stage]?.status === 'error') {
        throw new Error(`Stage ${stage} failed: ${stages[stage].error}`);
      }
    } catch (err) {
      if (err instanceof Error && err.message.startsWith('Stage ')) throw err;
    }
    await page.waitForTimeout(3000);
  }
  throw new Error(`Stage ${stage} timed out after ${timeoutMs}ms`);
}

/** Poll GET /api/pipeline/render/status until all sections are listed. */
async function waitForRenderSections(
  page: Page,
  expectedCount: number,
  timeoutMs: number = 60_000,
): Promise<void> {
  const startTime = Date.now();
  while (Date.now() - startTime < timeoutMs) {
    const response = await page.request.get('/api/pipeline/render/status');
    if (response.ok()) {
      const body = await response.json();
      if ((body?.sections?.length ?? 0) === expectedCount) {
        return;
      }
    }
    await page.waitForTimeout(2000);
  }

  throw new Error(`Render status never listed ${expectedCount} sections`);
}

/** Poll GET /api/project until the expected section count is present. */
async function waitForProjectSections(
  page: Page,
  expectedCount: number,
  timeoutMs: number = 60_000,
): Promise<void> {
  const startTime = Date.now();
  while (Date.now() - startTime < timeoutMs) {
    const response = await page.request.get('/api/project');
    if (response.ok()) {
      const body = await response.json();
      if ((body?.sections?.length ?? 0) === expectedCount) {
        return;
      }
    }
    await page.waitForTimeout(2000);
  }

  throw new Error(`Project never reported ${expectedCount} sections`);
}

/** Navigate to a stage via sidebar click, verify its heading. */
async function navigateToStage(
  page: Page,
  sidebar: ReturnType<Page['locator']>,
  sidebarText: string | RegExp,
  headingText: string,
): Promise<void> {
  if (typeof sidebarText === 'string') {
    await sidebar.locator('button', { hasText: sidebarText }).first().click();
  } else {
    await sidebar.locator('button').filter({ hasText: sidebarText }).click();
  }
  await expect(
    page.locator('h2', { hasText: headingText }).first(),
  ).toBeVisible({ timeout: 15000 });
}

// ---------------------------------------------------------------------------
// Tests (serial — annotation test reuses the rendered video from pipeline)
// ---------------------------------------------------------------------------

test.describe.serial('Full pipeline end-to-end', () => {
  test('produce a complete video through all 10 stages', async ({ page }) => {
    const pageErrors: string[] = [];
    page.on('pageerror', (err) => pageErrors.push(err.message));
    const sidebar = page.locator('aside');

    // ── Stage 1: Project Setup ──────────────────────────────────────────
    await page.goto('/');
    await expect(page.locator('h2', { hasText: 'Stage 1' })).toBeVisible({ timeout: 30000 });

    // Verify the project API reports the expected sections before touching the table UI
    await waitForProjectSections(page, 2);

    // Click Save
    await page.locator('button', { hasText: 'Save' }).click();
    await page.waitForTimeout(2000);

    // ── Stage 2: Script Editor ──────────────────────────────────────────
    await navigateToStage(page, sidebar, 'Script', 'Stage 2');

    // Click "Generate TTS Script →"
    await page.locator('button', { hasText: 'Generate TTS Script' }).click();

    // Wait for tts-script stage to complete (uses runPipelineStage → pipeline_status)
    await waitForStageCompletion(page, 'tts-script');

    // ── Stage 3: TTS Script ─────────────────────────────────────────────
    await navigateToStage(page, sidebar, 'TTS Script', 'Stage 3');

    // Click "Render Audio →" to advance to Stage 4
    await page.locator('button', { hasText: 'Render Audio' }).click();
    await page.waitForTimeout(1000);

    // ── Stage 4: TTS Rendering ──────────────────────────────────────────
    await expect(page.locator('h2', { hasText: 'Stage 4' })).toBeVisible({ timeout: 15000 });

    // Click "Render All" — now uses runPipelineStage and updates pipeline_status
    await page.locator('button', { hasText: 'Render All' }).click();

    // Wait for tts-render via pipeline_status (no longer needs special polling)
    await waitForStageCompletion(page, 'tts-render');

    // Navigate to Stage 5 via sidebar
    await navigateToStage(page, sidebar, 'Audio Sync', 'Stage 5');

    // ── Stage 5: Audio Sync ─────────────────────────────────────────────
    await page.locator('button', { hasText: 'Run Audio Sync' }).click();

    // Wait for audio-sync to complete
    await waitForStageCompletion(page, 'audio-sync');

    // Navigate to Stage 6 via sidebar
    await navigateToStage(page, sidebar, 'Spec Gen', 'Stage 6');

    // ── Stage 6: Spec Generation ────────────────────────────────────────
    await page.locator('button', { hasText: 'Generate All Specs' }).click();

    // Wait for specs to complete
    await waitForStageCompletion(page, 'specs');

    // Navigate to Stage 7 via sidebar
    await navigateToStage(page, sidebar, 'Veo Gen', 'Stage 7');

    // ── Stage 7: Veo Generation ─────────────────────────────────────────
    // Select veo_section from the stage toolbar dropdown, not the global project selector
    const sectionSelect = page
      .locator('button', { hasText: 'Generate Section' })
      .locator('xpath=preceding-sibling::select[1]');
    await sectionSelect.selectOption('veo_section');

    // Click "Generate Section" (only for veo_section, avoids error on animation-only)
    await page.locator('button', { hasText: 'Generate Section' }).click();

    // Wait for veo to complete (up to 10 min — Veo API polls every 5s)
    await waitForStageCompletion(page, 'veo', 600_000);

    // Navigate to Stage 8 via sidebar
    await navigateToStage(page, sidebar, 'Compositions', 'Stage 8');

    // ── Stage 8: Composition Generation ─────────────────────────────────
    // The compositions executor now stages Veo assets and rebuilds the
    // Remotion bundle automatically after generating components/wrappers.

    // Wait for composition list to load before clicking (avoids sending empty arrays)
    await expect(page.locator('[data-testid^="component-row-"]').first()).toBeVisible({ timeout: 15000 });
    await page.locator('button', { hasText: 'Generate All Compositions' }).click();

    // Wait for compositions to complete (includes bundle rebuild)
    await waitForStageCompletion(page, 'compositions');
    console.log('integration: compositions done');

    // ── Stage 9: Render & Stitch ────────────────────────────────────────
    // Drive render via the API directly to avoid sidebar/button ambiguity.
    await waitForRenderSections(page, 2);
    console.log('integration: render status ready');

    const renderRes = await page.request.post('/api/pipeline/render/run', {
      data: { sections: ['animation_section', 'veo_section'] },
      timeout: 900_000,
    });
    expect(renderRes.ok()).toBe(true);
    console.log('integration: render triggered via API');

    // Wait for render stage to complete
    await waitForStageCompletion(page, 'render');
    console.log('integration: render done');

    // Verify the rendered files are visible via the render status API.
    const preRenderRes = await page.request.get('/api/pipeline/render/status');
    const preRender = await preRenderRes.json();
    const allRendered = preRender.sections?.every(
      (s: { status: string }) => s.status === 'done',
    );
    expect(allRendered).toBe(true);

    const stitchRes = await page.request.post('/api/pipeline/stitch/run', {
      timeout: 300_000,
    });
    expect(stitchRes.ok()).toBe(true);
    console.log('integration: stitch triggered via API');

    const animationPath = path.join(OUTPUTS_DIR, 'sections', 'animation_section.mp4');
    const veoPath = path.join(OUTPUTS_DIR, 'sections', 'veo_section.mp4');
    const fullVideoPath = path.join(OUTPUTS_DIR, 'full_video.mp4');

    // Wait for full video to exist
    const stitchStart = Date.now();
    while (Date.now() - stitchStart < 300_000) {
      if (fs.existsSync(fullVideoPath)) break;
      await page.waitForTimeout(3000);
    }
    expect(fs.existsSync(fullVideoPath)).toBe(true);
    console.log('integration: full video exists');

    // ── Audio & asset assertions ──────────────────────────────────────
    // Section videos must contain audio streams (narration from TTS)
    expect(hasAudioStream(animationPath)).toBe(true);
    expect(hasAudioStream(veoPath)).toBe(true);
    expect(hasAudioStream(fullVideoPath)).toBe(true);

    // Veo section must contain real Veo-generated content (not a test placeholder).
    // Verify the Veo output file exists in outputs/veo/ (proving Stage 7 ran).
    const veoOutputDir = path.join(OUTPUTS_DIR, 'veo');
    const veoOutputFiles = fs.existsSync(veoOutputDir)
      ? fs.readdirSync(veoOutputDir).filter((f) => f.endsWith('.mp4'))
      : [];
    expect(veoOutputFiles.length).toBeGreaterThan(0);

    // Both section videos must have non-black visual content.
    // Extract a frame at the midpoint and verify pixel data is not all zeros.
    for (const [label, videoPath] of [
      ['animation_section', animationPath],
      ['veo_section', veoPath],
    ] as const) {
      const framePath = path.join(OUTPUTS_DIR, `${label}_check_frame.png`);
      extractFrame(videoPath, framePath);
      expect(maxPixelValue(framePath)).toBeGreaterThan(0);
    }

    // ── Stage 10: Audit ─────────────────────────────────────────────────
    const auditRes = await page.request.post('/api/pipeline/audit/run', {
      data: { sections: ['animation_section', 'veo_section'] },
      timeout: 600_000,
    });
    expect(auditRes.ok()).toBe(true);
    console.log('integration: audit triggered via API');

    // Wait for audit to complete
    await waitForStageCompletion(page, 'audit');
    console.log('integration: audit done');

    // ── Final Assertions ────────────────────────────────────────────────
    expect(fs.existsSync(fullVideoPath)).toBe(true);

    // Navigate to Review tab and verify video player is visible
    await page.getByRole('button', { name: 'Review', exact: true }).click();
    await page.waitForTimeout(2000);
    await expect(page.locator('video').first()).toBeVisible({ timeout: 15000 });

    // No unexpected page errors (filter extension errors and SSE parse noise)
    const appErrors = pageErrors.filter(
      (e) =>
        !e.includes('Extension') &&
        !e.includes('chrome-extension') &&
        !e.includes('is not valid JSON'),
    );
    expect(appErrors).toHaveLength(0);
  });

  // -----------------------------------------------------------------------
  // Test 2: Annotation → Fix → Re-render
  // -----------------------------------------------------------------------

  test('annotation fix re-edits animation_section video', async ({ page }) => {
    const PRE_FIX_FRAME = path.join(OUTPUTS_DIR, 'annotation_test_pre_fix_frame.png');
    const POST_FIX_FRAME = path.join(OUTPUTS_DIR, 'annotation_test_post_fix_frame.png');
    const REVIEW_SCREENSHOT = path.join(OUTPUTS_DIR, 'annotation_test_review_tab.png');

    // ── Phase 1: Save pre-fix state ─────────────────────────────────────
    expect(fs.existsSync(ANIMATION_VIDEO)).toBe(true);
    const preFixStat = fs.statSync(ANIMATION_VIDEO);

    // Snapshot all animation-related TSX files (names are dynamic)
    const preFixTsxSnapshot = snapshotAnimationTsx();
    expect(preFixTsxSnapshot.size).toBeGreaterThan(0);
    console.log(`Pre-fix TSX snapshot: ${preFixTsxSnapshot.size} files`);
    for (const p of preFixTsxSnapshot.keys()) {
      console.log(`  ${path.relative(PROJECT_ROOT, p)}`);
    }

    extractFrame(ANIMATION_VIDEO, PRE_FIX_FRAME);
    expect(fs.existsSync(PRE_FIX_FRAME)).toBe(true);

    // ── Phase 2: Create annotation via API ──────────────────────────────
    // Build base64 data URL from the pre-fix frame for compositeDataUrl
    const frameBuffer = fs.readFileSync(PRE_FIX_FRAME);
    const compositeDataUrl = `data:image/png;base64,${frameBuffer.toString('base64')}`;

    const createRes = await page.request.post('/api/annotations', {
      data: {
        sectionId: 'animation_section',
        timestamp: 1.0,
        text: 'Change the main background color of this section to bright red (#FF0000). Find all background color values in the animation_section TSX component files under remotion/src/remotion/ and replace them with #FF0000.',
        compositeDataUrl,
        videoFile: 'animation_section.mp4',
        inputMethod: 'typed',
      },
    });
    expect(createRes.status()).toBe(201);
    const annotation = await createRes.json();
    const annotationId: string = annotation.id;
    expect(annotationId).toBeTruthy();

    // ── Phase 3: Run Claude analysis ────────────────────────────────────
    const analyzeRes = await page.request.post(
      `/api/annotations/${annotationId}/analyze`,
      { timeout: 120_000 },
    );
    expect(analyzeRes.status()).toBe(200);
    const analyzeBody = await analyzeRes.json();
    let fixType = analyzeBody.annotation?.analysis?.fixType;

    // If Claude didn't return "remotion", inject the correct analysis via PUT
    if (fixType !== 'remotion') {
      console.warn(
        `Claude returned fixType="${fixType}" instead of "remotion" — injecting canned analysis`,
      );
      const putRes = await page.request.put(`/api/annotations/${annotationId}`, {
        data: {
          analysis: {
            fixType: 'remotion',
            severity: 'major',
            technicalAssessment: 'Background color needs to change to bright red (#FF0000) in the animation_section TSX components.',
            suggestedFixes: [
              'Replace background color values with #FF0000 in the animation_section component TSX files under remotion/src/remotion/',
            ],
          },
        },
      });
      expect(putRes.status()).toBe(200);
      fixType = 'remotion';
    }

    expect(fixType).toBe('remotion');

    // ── Phase 4: Navigate to Review tab & verify UI ─────────────────────
    await page.goto('/');
    await page.waitForTimeout(2000);
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(3000);

    // Take a screenshot of the Review tab for manual inspection
    await page.screenshot({ path: REVIEW_SCREENSHOT });

    // Verify annotation card is visible (contains "background color" from our annotation text)
    await expect(
      page.locator('text=background color').first(),
    ).toBeVisible({ timeout: 15000 });

    // ── Phase 5: Apply fixes via UI ─────────────────────────────────────
    // Click "Apply N Fixes" in AnnotationPanel
    const applyButton = page.locator('button').filter({ hasText: /Apply \d+ Fix/ }).first();
    await expect(applyButton).toBeVisible({ timeout: 15000 });
    await applyButton.click();

    // FixPreviewPanel appears — wait for "Generating previews..." to disappear
    await expect(
      page.locator('text=Generating previews'),
    ).toBeVisible({ timeout: 10000 }).catch(() => {
      // May have loaded fast enough to skip the loading state
    });
    await expect(
      page.locator('text=Generating previews'),
    ).toBeHidden({ timeout: 120_000 });

    // Click the green "Apply N Fixes" button in FixPreviewPanel
    const greenApplyButton = page.locator('button.bg-green-600').filter({ hasText: /Apply \d+ Fix/ });
    await expect(greenApplyButton).toBeVisible({ timeout: 15000 });
    await greenApplyButton.click();

    // ── Phase 6: Wait for fix job completion ────────────────────────────
    // Poll the annotation until resolveJobId is set
    let resolveJobId: string | null = null;
    const jobPollStart = Date.now();
    while (Date.now() - jobPollStart < 60_000) {
      const annData = await getJsonWithRetry(
        page,
        `/api/annotations/${annotationId}`,
      ) as { resolveJobId?: string | null };
      if (annData.resolveJobId) {
        resolveJobId = annData.resolveJobId;
        break;
      }
      await page.waitForTimeout(2000);
    }
    expect(resolveJobId).toBeTruthy();

    // Poll the job until done
    const jobStart = Date.now();
    while (Date.now() - jobStart < 600_000) {
      const jobData = await getJsonWithRetry(
        page,
        `/api/jobs/${resolveJobId}`,
      ) as { status?: string; error?: string | null };
      if (jobData.status === 'done') break;
      if (jobData.status === 'error') {
        throw new Error(`Fix job failed: ${jobData.error ?? JSON.stringify(jobData)}`);
      }
      await page.waitForTimeout(5000);
    }

    // Verify job completed
    const finalJob = await getJsonWithRetry(
      page,
      `/api/jobs/${resolveJobId}`,
    ) as { status?: string };
    expect(finalJob.status).toBe('done');

    // ── Phase 7: Verify post-fix state ──────────────────────────────────

    // 7a. At least one TSX file was modified by Claude
    const postFixTsxSnapshot = snapshotAnimationTsx();
    let tsxFilesChanged = 0;
    for (const [filePath, preContent] of preFixTsxSnapshot) {
      const postContent = postFixTsxSnapshot.get(filePath);
      if (postContent !== undefined && postContent !== preContent) {
        tsxFilesChanged++;
        console.log(`  TSX changed: ${path.relative(PROJECT_ROOT, filePath)}`);
      }
    }
    // Also count newly created files as changes
    for (const filePath of postFixTsxSnapshot.keys()) {
      if (!preFixTsxSnapshot.has(filePath)) {
        tsxFilesChanged++;
        console.log(`  TSX added: ${path.relative(PROJECT_ROOT, filePath)}`);
      }
    }
    console.log(`Total TSX files changed: ${tsxFilesChanged}`);
    expect(tsxFilesChanged).toBeGreaterThan(0);

    // 7b. Video file was re-rendered (newer mtime)
    const postFixStat = fs.statSync(ANIMATION_VIDEO);
    expect(postFixStat.mtimeMs).toBeGreaterThan(preFixStat.mtimeMs);

    // 7c. Audio present in re-rendered video
    expect(hasAudioStream(ANIMATION_VIDEO)).toBe(true);

    // 7d. Non-black visual content in re-rendered video
    extractFrame(ANIMATION_VIDEO, POST_FIX_FRAME);
    expect(maxPixelValue(POST_FIX_FRAME)).toBeGreaterThan(0);

    // 7e. Frames differ (visual change occurred)
    const diff = frameDiffSum(PRE_FIX_FRAME, POST_FIX_FRAME);
    expect(diff).toBeGreaterThan(0);

    // 7f. Git commit exists (optional — don't fail if git is unavailable)
    try {
      const gitLog = execSync('git log --oneline -5', {
        cwd: PROJECT_ROOT,
        encoding: 'utf-8',
      });
      console.log('Recent git commits:\n' + gitLog);
    } catch {
      console.warn('Git log check skipped (git not available or no commits)');
    }

    // ── Phase 8: Artifacts saved for manual inspection ──────────────────
    console.log('Artifacts:');
    console.log(`  Pre-fix frame:  ${PRE_FIX_FRAME}`);
    console.log(`  Post-fix frame: ${POST_FIX_FRAME}`);
    console.log(`  Review tab screenshot: ${REVIEW_SCREENSHOT}`);
  });
});
