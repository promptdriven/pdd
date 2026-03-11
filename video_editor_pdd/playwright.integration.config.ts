import { defineConfig } from '@playwright/test';

const INTEGRATION_PORT = 3101;

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
    baseURL: `http://localhost:${INTEGRATION_PORT}`,
    screenshot: 'only-on-failure',
    trace: 'retain-on-failure',
  },
  webServer: {
    command: 'npx tsx e2e/tests/integration/start-server.ts',
    port: INTEGRATION_PORT,
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
