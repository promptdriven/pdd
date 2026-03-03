/** @type {import('jest').Config} */
const config = {
  testEnvironment: "node",
  transform: {
    "^.+\\.(ts|tsx)$": ["ts-jest", { tsconfig: "tsconfig.test.json", diagnostics: false }],
  },
  testMatch: ["<rootDir>/tests/integration/test_remotion_environment.ts"],
  moduleNameMapper: {
    "^@/(.*)$": "<rootDir>/$1",
    "^server-only$": "<rootDir>/__mocks__/server-only.js",
  },
};

module.exports = config;
