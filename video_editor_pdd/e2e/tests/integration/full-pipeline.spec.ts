import { test, expect, Page } from '@playwright/test';
import fs from 'fs';
import path from 'path';

const PROJECT_ROOT = path.resolve(__dirname, '..', '..', '..');
const OUTPUTS_DIR = path.join(PROJECT_ROOT, 'outputs');

/** Use ffprobe to check whether a video file has an audio stream. */
function hasAudioStream(videoPath: string): boolean {
  try {
    const { execSync } = require('child_process');
    const result = execSync(
      `ffprobe -v quiet -select_streams a -show_entries stream=codec_type -of csv=p=0 "${videoPath}"`,
      { encoding: 'utf-8' },
    );
    return result.trim().includes('audio');
  } catch {
    return false;
  }
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

/** Navigate to a stage via sidebar click, verify its heading. */
async function navigateToStage(
  page: Page,
  sidebar: ReturnType<Page['locator']>,
  sidebarText: string | RegExp,
  headingText: string,
): Promise<void> {
  if (typeof sidebarText === 'string') {
    await sidebar.locator('div', { hasText: sidebarText }).first().click();
  } else {
    await sidebar.locator('div').filter({ hasText: sidebarText }).click();
  }
  await expect(
    page.locator('h2', { hasText: headingText }).first(),
  ).toBeVisible({ timeout: 15000 });
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

test.describe('Full pipeline end-to-end', () => {
  test('produce a complete video through all 10 stages', async ({ page }) => {
    const pageErrors: string[] = [];
    page.on('pageerror', (err) => pageErrors.push(err.message));
    const sidebar = page.locator('aside');

    // ── Stage 1: Project Setup ──────────────────────────────────────────
    await page.goto('/');
    await expect(page.locator('h2', { hasText: 'Stage 1' })).toBeVisible({ timeout: 30000 });

    // Verify 2 sections loaded
    await expect(page.locator('tbody tr')).toHaveCount(2);

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
    // Select veo_section from the dropdown
    const sectionSelect = page.locator('select').first();
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

    // Debug: read executor's debug log
    const compDebugLog = path.join(PROJECT_ROOT, 'outputs', 'compositions_debug.log');
    if (fs.existsSync(compDebugLog)) {
      console.log('[DEBUG] compositions_debug.log:\n' + fs.readFileSync(compDebugLog, 'utf-8'));
    } else {
      console.log('[DEBUG] compositions_debug.log: NOT FOUND');
    }
    // Debug: inspect generated components for this run
    const remotionDir = path.join(PROJECT_ROOT, 'remotion', 'src', 'remotion');
    for (const f of ['animation_section_main.tsx', 'veo_section_main.tsx']) {
      const fp = path.join(remotionDir, f);
      if (fs.existsSync(fp)) {
        const content = fs.readFileSync(fp, 'utf-8');
        console.log(`[DEBUG] ${f} (${content.length} chars):\n${content.slice(0, 500)}`);
      } else {
        console.log(`[DEBUG] ${f}: NOT FOUND`);
      }
    }
    // Check wrapper import
    const wrapperPath = path.join(remotionDir, 'animation_section', 'index.tsx');
    if (fs.existsSync(wrapperPath)) {
      console.log(`[DEBUG] wrapper:\n${fs.readFileSync(wrapperPath, 'utf-8')}`);
    }
    // Check project.json compositions
    const pj = JSON.parse(fs.readFileSync(path.join(PROJECT_ROOT, 'project.json'), 'utf-8'));
    for (const s of pj.sections) {
      console.log(`[DEBUG] project.json ${s.id}: compositions=${JSON.stringify(s.compositions)}`);
    }

    // Navigate to Stage 9 via sidebar
    await navigateToStage(page, sidebar, /^9\s*Render/, 'Stage 9');

    // ── Stage 9: Render & Stitch ────────────────────────────────────────
    // Wait for sections to load from the status API before clicking Render
    await expect(page.locator('tbody tr')).toHaveCount(2, { timeout: 15000 });

    // Click "Render All" to render sections via the pipeline (now uses
    // child process instead of in-process renderMedia, so it won't hang).
    await page.locator('button', { hasText: 'Render' }).first().click();

    // Wait for render stage to complete
    await waitForStageCompletion(page, 'render');

    // Verify the rendered files are visible via the render status API.
    const preRenderRes = await page.request.get('/api/pipeline/render/status');
    const preRender = await preRenderRes.json();
    const allRendered = preRender.sections?.every(
      (s: { status: string }) => s.status === 'done',
    );
    expect(allRendered).toBe(true);

    // Click "Stitch Full Video"
    await page.locator('button', { hasText: 'Stitch Full Video' }).click();

    // Wait for full video to exist
    const stitchStart = Date.now();
    while (Date.now() - stitchStart < 300_000) {
      const res = await page.request.get('/api/pipeline/render/status');
      const data = await res.json();
      if (data.fullVideo?.exists) break;
      await page.waitForTimeout(3000);
    }

    // Verify full video exists via API
    const renderStatusRes = await page.request.get('/api/pipeline/render/status');
    const renderStatus = await renderStatusRes.json();
    expect(renderStatus.fullVideo.exists).toBe(true);

    // ── Audio & asset assertions ──────────────────────────────────────
    // Section videos must contain audio streams (narration from TTS)
    const animationPath = path.join(OUTPUTS_DIR, 'sections', 'animation_section.mp4');
    const veoPath = path.join(OUTPUTS_DIR, 'sections', 'veo_section.mp4');
    const fullVideoPath = path.join(OUTPUTS_DIR, 'full_video.mp4');

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
    const { execSync: execSyncLocal } = require('child_process');
    for (const [label, videoPath] of [
      ['animation_section', animationPath],
      ['veo_section', veoPath],
    ] as const) {
      const framePath = path.join(OUTPUTS_DIR, `${label}_check_frame.png`);
      execSyncLocal(
        `ffmpeg -y -ss 1 -i "${videoPath}" -vframes 1 -update 1 "${framePath}"`,
        { stdio: 'pipe' },
      );
      // Read PNG and check that at least some pixels are non-zero
      const pixelCheck = execSyncLocal(
        `python3 -c "from PIL import Image; import numpy as np; img=np.array(Image.open('${framePath}')); print(img.max())"`,
        { encoding: 'utf-8' },
      ).trim();
      expect(parseInt(pixelCheck, 10)).toBeGreaterThan(0,
        // @ts-expect-error -- custom message
        `${label} video is all black (no visual content)`,
      );
    }

    // ── Stage 10: Audit ─────────────────────────────────────────────────
    await navigateToStage(page, sidebar, /^10\s*Audit/, 'Audit Results');

    // Click "Audit All Sections"
    await page.locator('button', { hasText: 'Audit All Sections' }).click();

    // Wait for audit to complete
    await waitForStageCompletion(page, 'audit');

    // ── Final Assertions ────────────────────────────────────────────────
    const finalRenderRes = await page.request.get('/api/pipeline/render/status');
    const finalRender = await finalRenderRes.json();
    expect(finalRender.fullVideo.exists).toBe(true);

    // Navigate to Review tab and verify video player is visible
    await page.locator('button', { hasText: 'Review' }).click();
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
});
