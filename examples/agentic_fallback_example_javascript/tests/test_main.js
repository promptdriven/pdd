#!/usr/bin/env node
const assert = require('assert');
const { execSync } = require('child_process');
const path = require('path');
const utils = require('../src/utils');

function testUtilsAddReturnsFive() {
    // Should compile against utils.add(a,b) and return 5.
    const result = utils.add(2, 3);
    assert.strictEqual(result, 5, 'utils.add(2,3) must return 5');
}

function testMainPrintsFive() {
    // Main should print the computed sum (5) followed by a newline.
    const mainPath = path.join(__dirname, '../src/main.js');
    const output = execSync(`node ${JSON.stringify(mainPath)}`).toString().trim();
    assert.strictEqual(output, '5', 'main.js should print 5');
}

// Run tests
try {
    testUtilsAddReturnsFive();
    testMainPrintsFive();
    console.log('All tests passed!');
} catch (error) {
    console.error('Test failed:', error.message);
    process.exit(1);
}
