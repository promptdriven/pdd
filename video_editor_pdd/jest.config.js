/** @type {import('jest').Config} */
const config = {
  testEnvironment: "node",
  transform: {
    "^.+\\.(ts|tsx)$": ["ts-jest", { tsconfig: "tsconfig.test.json", diagnostics: false }],
  },
  testMatch: ["**/__tests__/**/*.test.ts", "**/*.test.ts", "**/tests/**/*.ts", "**/tests/**/*.tsx", "tests/*.ts", "tests/*.tsx"],
  testPathIgnorePatterns: ["/node_modules/", "/e2e/"],
  moduleNameMapper: {
    "^@/(.*)$": "<rootDir>/$1",
    "^server-only$": "<rootDir>/__mocks__/server-only.js",
  },
};

module.exports = config;
