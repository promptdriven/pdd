module.exports = {
  testEnvironment: 'node',
  testMatch: ['**/test/**/*.test.js'],
  moduleNameMapper: {
    '^@/(.*)$': '<rootDir>/$1',
  },
};
