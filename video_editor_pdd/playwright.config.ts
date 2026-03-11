import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './e2e/tests',
  testIgnore: ['**/integration/**'],
  timeout: 30000,
  expect: {
    timeout: 10000,
  },
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 1,
  workers: process.env.CI ? 1 : 4,
  reporter: [['list'], ['html', { outputFolder: 'playwright-report' }]],
  outputDir: 'test-results/',
  use: {
    baseURL: 'http://localhost:3001',
    screenshot: 'only-on-failure',
    trace: 'on-first-retry',
  },
  webServer: {
    command: 'VIDEO_EDITOR_PROJECT_ID=video_editor_pdd CLAUDE_FIX_MODEL=claude-sonnet-4-5 CLAUDE_DRY_RUN_MODEL=claude-sonnet-4-5 PDD_DETERMINISTIC_PIPELINE=1 VIDEO_EDITOR_SKIP_COMPOSITION_VALIDATION=1 npx next build && VIDEO_EDITOR_PROJECT_ID=video_editor_pdd CLAUDE_FIX_MODEL=claude-sonnet-4-5 CLAUDE_DRY_RUN_MODEL=claude-sonnet-4-5 PDD_DETERMINISTIC_PIPELINE=1 VIDEO_EDITOR_SKIP_COMPOSITION_VALIDATION=1 npx next start -p 3001',
    port: 3001,
    reuseExistingServer: false,
    timeout: 180_000,
  },
  projects: [
    {
      name: 'chromium',
      use: {
        browserName: 'chromium',
      },
    },
  ],
});
