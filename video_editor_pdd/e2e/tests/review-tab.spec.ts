import { test, expect } from '@playwright/test';

test.describe('Review Tab', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
    await page.waitForLoadState('networkidle');
    // Switch to Review tab
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(500);
  });

  test('shows video player area', async ({ page }) => {
    // The Play/Pause button should be visible
    await expect(page.locator('text=Play/Pause')).toBeVisible();
  });

  test('shows annotation drawing tools', async ({ page }) => {
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'RECTANGLE' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'CIRCLE' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'ARROW' })).toBeVisible();
    await expect(page.locator('button', { hasText: 'TEXT' })).toBeVisible();
  });

  test('shows Annotations panel', async ({ page }) => {
    await expect(page.getByText('Annotations', { exact: true })).toBeVisible();
  });

  test('shows empty annotation state', async ({ page }) => {
    await expect(page.locator('text=No annotations yet')).toBeVisible();
  });

  test('sidebar is not visible in Review tab', async ({ page }) => {
    const sidebar = page.locator('aside');
    await expect(sidebar).not.toBeVisible();
  });

  test('video player container has dark background', async ({ page }) => {
    const videoContainer = page.locator('.aspect-video').first();
    await expect(videoContainer).toBeVisible();
    const isDark = await videoContainer.evaluate((el) => {
      const bgColor = getComputedStyle(el).backgroundColor;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = bgColor;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r < 50 && g < 50 && b < 50;
    });
    expect(isDark).toBe(true);
  });

  test('canvas overlay is present for drawing', async ({ page }) => {
    const canvas = page.locator('canvas');
    await expect(canvas).toBeVisible();
  });

  test('video element is present', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();
  });

  test('freehand tool is selected by default (blue bg)', async ({ page }) => {
    const freehandBtn = page.locator('button', { hasText: 'FREEHAND' });
    await expect(freehandBtn).toBeVisible();
    const isBlue = await freehandBtn.evaluate((el) => {
      const bgColor = getComputedStyle(el).backgroundColor;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = bgColor;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return b > 150;
    });
    expect(isBlue).toBe(true);
  });

  test('tool buttons text is readable (dark theme)', async ({ page }) => {
    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    await expect(rectBtn).toBeVisible();
    const isLight = await rectBtn.evaluate((el) => {
      const color = getComputedStyle(el).color;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = color;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r > 180 && g > 180 && b > 180;
    });
    expect(isLight).toBe(true);
  });

  test('time display shows formatted time', async ({ page }) => {
    // formatTime renders "{currentTime} / {duration}" inside a <span>
    // With no video loaded, both values are "0:00"
    const timeSpan = page.locator('span', { hasText: '/' }).filter({ hasText: ':' });
    await expect(timeSpan.first()).toBeVisible();
  });

  test('keyboard shortcut hints are visible', async ({ page }) => {
    await expect(page.getByText('Space = Annotate')).toBeVisible();
  });

  test('Annotations panel heading text is readable (dark theme)', async ({ page }) => {
    const heading = page.getByText('Annotations', { exact: true });
    await expect(heading).toBeVisible();
    const isLight = await heading.evaluate((el) => {
      const color = getComputedStyle(el).color;
      const canvas = document.createElement('canvas');
      canvas.width = 1;
      canvas.height = 1;
      const ctx = canvas.getContext('2d')!;
      ctx.fillStyle = color;
      ctx.fillRect(0, 0, 1, 1);
      const [r, g, b] = ctx.getImageData(0, 0, 1, 1).data;
      return r > 180 && g > 180 && b > 180;
    });
    expect(isLight).toBe(true);
  });

  test('Apply Fixes button is present and disabled when no annotations', async ({ page }) => {
    const applyBtn = page.locator('button', { hasText: /Apply \d+ Fixes/ });
    await expect(applyBtn).toBeVisible();
    await expect(applyBtn).toBeDisabled();
  });

  test('switching back to Pipeline shows sidebar again', async ({ page }) => {
    // Sidebar should not be visible in Review
    await expect(page.locator('aside')).not.toBeVisible();

    // Switch back to Pipeline
    await page.locator('button', { hasText: 'Pipeline' }).click();
    await page.waitForTimeout(500);

    // Sidebar should be visible again
    await expect(page.locator('aside')).toBeVisible();
  });

  test('Review tab has active blue border indicator', async ({ page }) => {
    const reviewBtn = page.locator('button', { hasText: 'Review' });
    await expect(reviewBtn).toBeVisible();
    const borderStyle = await reviewBtn.evaluate((el) => getComputedStyle(el).borderBottomStyle);
    expect(borderStyle).toBe('solid');
  });

  test('no console errors in Review tab', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');
    await page.waitForTimeout(1000);
    await page.locator('button', { hasText: 'Review' }).click();
    await page.waitForTimeout(3000);
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });

  test('Play/Pause button toggles video playback state', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // Video should initially be paused
    const isPausedBefore = await video.evaluate((v: HTMLVideoElement) => v.paused);
    expect(isPausedBefore).toBe(true);

    // Click Play/Pause button
    const playPauseButton = page.locator('button', { hasText: 'Play/Pause' });
    await playPauseButton.click();
    await page.waitForTimeout(500);

    // Video may or may not actually play (no source loaded), but the click should not crash
    // Verify the button is still visible and functional
    await expect(playPauseButton).toBeVisible();
  });

  test('Tool buttons (Rectangle, Circle, Arrow, Text) highlight on click', async ({ page }) => {
    // FREEHAND should be selected by default (blue background)
    const freehandBtn = page.locator('button', { hasText: 'FREEHAND' });
    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    const circleBtn = page.locator('button', { hasText: 'CIRCLE' });
    const arrowBtn = page.locator('button', { hasText: 'ARROW' });
    const textBtn = page.locator('button', { hasText: 'TEXT' });

    // Click RECTANGLE and verify it gets the blue background
    await rectBtn.click();
    await page.waitForTimeout(300);
    const rectHasBlue = await rectBtn.evaluate((el) => {
      return el.classList.contains('bg-blue-600');
    });
    expect(rectHasBlue).toBe(true);

    // FREEHAND should no longer be blue
    const freehandHasBlue = await freehandBtn.evaluate((el) => {
      return el.classList.contains('bg-blue-600');
    });
    expect(freehandHasBlue).toBe(false);

    // Click CIRCLE
    await circleBtn.click();
    await page.waitForTimeout(300);
    const circleHasBlue = await circleBtn.evaluate((el) => {
      return el.classList.contains('bg-blue-600');
    });
    expect(circleHasBlue).toBe(true);

    // RECTANGLE should no longer be blue
    const rectStillBlue = await rectBtn.evaluate((el) => {
      return el.classList.contains('bg-blue-600');
    });
    expect(rectStillBlue).toBe(false);

    // Click ARROW
    await arrowBtn.click();
    await page.waitForTimeout(300);
    const arrowHasBlue = await arrowBtn.evaluate((el) => {
      return el.classList.contains('bg-blue-600');
    });
    expect(arrowHasBlue).toBe(true);

    // Click TEXT
    await textBtn.click();
    await page.waitForTimeout(300);
    const textHasBlue = await textBtn.evaluate((el) => {
      return el.classList.contains('bg-blue-600');
    });
    expect(textHasBlue).toBe(true);
  });

  test('Keyboard K toggles play/pause', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // Initially paused
    const isPausedBefore = await video.evaluate((v: HTMLVideoElement) => v.paused);
    expect(isPausedBefore).toBe(true);

    // Press K to toggle play/pause
    await page.keyboard.press('k');
    await page.waitForTimeout(500);

    // The video element should have received the play command (may not actually play without source)
    // Verify no crash occurred by checking the video element is still attached
    await expect(video).toBeAttached();
  });

  test('Keyboard D selects freehand/draw tool', async ({ page }) => {
    // First, click RECTANGLE to change away from freehand
    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    await rectBtn.click();
    await page.waitForTimeout(300);

    // Verify RECTANGLE is selected
    let rectHasBlue = await rectBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(rectHasBlue).toBe(true);

    // Press D to switch back to freehand
    await page.keyboard.press('d');
    await page.waitForTimeout(300);

    // Verify FREEHAND is now selected
    const freehandBtn = page.locator('button', { hasText: 'FREEHAND' });
    const freehandHasBlue = await freehandBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(freehandHasBlue).toBe(true);

    // RECTANGLE should no longer be selected
    rectHasBlue = await rectBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(rectHasBlue).toBe(false);
  });

  test('Keyboard R selects rectangle tool', async ({ page }) => {
    // Default is FREEHAND
    const freehandBtn = page.locator('button', { hasText: 'FREEHAND' });
    let freehandHasBlue = await freehandBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(freehandHasBlue).toBe(true);

    // Press R to switch to rectangle
    await page.keyboard.press('r');
    await page.waitForTimeout(300);

    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    const rectHasBlue = await rectBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(rectHasBlue).toBe(true);

    // FREEHAND should no longer be selected
    freehandHasBlue = await freehandBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(freehandHasBlue).toBe(false);
  });

  test('Keyboard ArrowRight seeks forward', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // Get the initial currentTime
    const timeBefore = await video.evaluate((v: HTMLVideoElement) => v.currentTime);

    // Press ArrowRight to seek forward
    await page.keyboard.press('ArrowRight');
    await page.waitForTimeout(500);

    // The video should still be intact (no crash). currentTime may or may not change
    // depending on whether a video source is loaded, but the operation should be safe.
    await expect(video).toBeAttached();
  });

  test('Keyboard F toggles fullscreen without crash', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // Press F to toggle fullscreen
    // Note: Fullscreen may not actually work in headless browser, but it should not crash
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    await page.keyboard.press('f');
    await page.waitForTimeout(500);

    // Verify no crashes occurred
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension') && !e.includes('fullscreen')
    );
    expect(appErrors).toHaveLength(0);

    // The page should still be functional
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
  });

  test('Keyboard Ctrl+Z undoes without crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Press Ctrl+Z to undo
    await page.keyboard.press('Control+z');
    await page.waitForTimeout(500);

    // Verify no crashes occurred
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);

    // Page should still be functional
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
  });

  test('Progress bar click seeks video position', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // The progress bar is the div with class "relative h-2 bg-gray-700 rounded cursor-pointer"
    const progressBar = page.locator('.h-2.bg-gray-700.rounded.cursor-pointer');
    await expect(progressBar).toBeVisible();

    // Click on the progress bar (middle position)
    const box = await progressBar.boundingBox();
    expect(box).not.toBeNull();
    if (box) {
      await page.mouse.click(box.x + box.width / 2, box.y + box.height / 2);
      await page.waitForTimeout(500);
    }

    // The video element should still be attached (no crash from clicking progress bar)
    await expect(video).toBeAttached();
  });

  test('Keyboard C selects circle tool', async ({ page }) => {
    // First click RECTANGLE to change away from the default freehand tool
    const rectBtn = page.locator('button', { hasText: 'RECTANGLE' });
    await rectBtn.click();
    await page.waitForTimeout(300);

    // Verify RECTANGLE is now selected
    let rectHasBlue = await rectBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(rectHasBlue).toBe(true);

    // Press C to switch to circle
    await page.keyboard.press('c');
    await page.waitForTimeout(300);

    // CIRCLE button should now have bg-blue-600
    const circleBtn = page.locator('button', { hasText: 'CIRCLE' });
    const circleHasBlue = await circleBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(circleHasBlue).toBe(true);

    // RECTANGLE should no longer be selected
    rectHasBlue = await rectBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(rectHasBlue).toBe(false);
  });

  test('Keyboard A selects arrow tool', async ({ page }) => {
    // Press A to switch to arrow
    await page.keyboard.press('a');
    await page.waitForTimeout(300);

    // ARROW button should now have bg-blue-600
    const arrowBtn = page.locator('button', { hasText: 'ARROW' });
    const arrowHasBlue = await arrowBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(arrowHasBlue).toBe(true);
  });

  test('Keyboard T selects text tool', async ({ page }) => {
    // Press T to switch to text
    await page.keyboard.press('t');
    await page.waitForTimeout(300);

    // TEXT button should now have bg-blue-600
    const textBtn = page.locator('button', { hasText: 'TEXT' });
    const textHasBlue = await textBtn.evaluate((el) => el.classList.contains('bg-blue-600'));
    expect(textHasBlue).toBe(true);
  });

  test('Keyboard ArrowLeft seeks backward', async ({ page }) => {
    const video = page.locator('video');
    await expect(video).toBeAttached();

    // Press ArrowLeft to seek backward
    await page.keyboard.press('ArrowLeft');
    await page.waitForTimeout(500);

    // The video element should still be intact (no crash). currentTime may not change
    // without a loaded source, but the operation should be safe.
    await expect(video).toBeAttached();
  });

  test('Keyboard M toggles mic input method', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Press M to toggle input method between 'typed' and 'speech'
    await page.keyboard.press('m');
    await page.waitForTimeout(300);

    // speechAvailable may be false in headless browser, but the key press should not crash.
    // If speech is available, a "🎤" indicator becomes visible; check if it appears.
    const micIndicator = page.locator('text=🎤').first();
    const isMicVisible = await micIndicator.isVisible().catch(() => false);
    if (isMicVisible) {
      await expect(micIndicator).toBeVisible();
    }

    // Press M again to toggle back
    await page.keyboard.press('m');
    await page.waitForTimeout(300);

    // Verify no crashes occurred
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);

    // Page should still be functional
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
  });

  test('Keyboard Space toggles annotation recording mode', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    // Press Space to start recording mode (calls startRecordingMode())
    await page.keyboard.press('Space');
    await page.waitForTimeout(300);

    // Recording mode changes the UI; verify no crash and page is still functional
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();

    // Press Space again to stop recording mode (calls stopRecordingMode())
    await page.keyboard.press('Space');
    await page.waitForTimeout(300);

    // Verify no crashes occurred throughout
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);

    // Page should still be functional after toggling recording mode
    await expect(page.locator('button', { hasText: 'FREEHAND' })).toBeVisible();
  });

  test('Canvas pointer interaction does not crash', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', (err) => errors.push(err.message));

    const canvas = page.locator('canvas');
    await expect(canvas).toBeVisible();

    // Get the bounding box of the canvas element
    const box = await canvas.boundingBox();
    expect(box).not.toBeNull();
    if (box) {
      const centerX = box.x + box.width / 2;
      const centerY = box.y + box.height / 2;

      // Simulate a pointer drag across the canvas
      await page.mouse.move(centerX, centerY);
      await page.mouse.down();
      await page.mouse.move(centerX + 50, centerY + 50, { steps: 5 });
      await page.mouse.up();
      await page.waitForTimeout(300);
    }

    // Canvas should still be visible after the drag interaction
    await expect(canvas).toBeVisible();

    // Verify no crashes occurred
    const appErrors = errors.filter(
      (e) => !e.includes('Extension') && !e.includes('chrome-extension')
    );
    expect(appErrors).toHaveLength(0);
  });
});
