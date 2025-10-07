#!/usr/bin/env ts-node
import { add } from '../src/utils';
import { execSync } from 'child_process';

describe('TypeScript Agentic Fallback Example', () => {
    test('utils.add(2, 3) should return 5', () => {
        expect(add(2, 3)).toBe(5);
    });

    test('main.ts should print 5 to the console', () => {
        const output = execSync('ts-node examples/agentic_fallback_example_typescript/src/main.ts').toString().trim();
        expect(output).toBe('5');
    });
});
