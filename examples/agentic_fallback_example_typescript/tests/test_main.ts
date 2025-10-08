#!/usr/bin/env ts-node
import { add } from '../src/utils';
import { execSync } from 'child_process';

// Jest-like test runner without dependencies
function describe(name: string, fn: () => void) {
    console.log(`\n${name}`);
    fn();
}

function test(name: string, fn: () => void) {
    try {
        fn();
        console.log(`  ✓ ${name}`);
    } catch (error) {
        console.log(`  ✗ ${name}`);
        console.error(`    ${error}`);
        process.exit(1);
    }
}

function expect(actual: any) {
    return {
        toBe(expected: any) {
            if (actual !== expected) {
                throw new Error(`Expected ${expected}, but got ${actual}`);
            }
        }
    };
}

describe('TypeScript Agentic Fallback Example', () => {
    test('utils.add(2, 3) should return 5', () => {
        expect(add(2, 3)).toBe(5);
    });

    test('main.ts should print 5 to the console', () => {
        const output = execSync('ts-node src/main.ts').toString().trim();
        expect(output).toBe('5');
    });
});
