import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './e2e/tests/integration',
  globalTeardown: './e2e/tests/integration/global-teardown.ts',
  timeout: 1_800_000,
  expect: {
    timeout: 600_000,
  },
  fullyParallel: false,
  workers: 1,
  retries: 0,
  reporter: [['list'], ['html', { outputFolder: 'playwright-report-integration' }]],
  outputDir: 'test-results-integration/',
  use: {
    baseURL: 'http://localhost:3001',
    screenshot: 'only-on-failure',
    trace: 'retain-on-failure',
  },
  webServer: {
    command: 'npx tsx e2e/tests/integration/start-server.ts',
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
