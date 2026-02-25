/**
 * Tests for US25 — Cost Dashboard Component
 *
 * Verifies that CostDashboard.tsx includes:
 *   1. 'use client' directive (Next.js client component)
 *   2. Fetches cost data from /api/costs
 *   3. Displays total cost summary
 *   4. Displays per-stage breakdown table
 *   5. Has a refresh button
 *   6. Handles loading state
 *   7. Handles error state
 *   8. Formats cost with dollar sign
 *   9. Formats tokens with K/M suffixes
 */

import fs from 'fs';
import path from 'path';

describe('CostDashboard component (US25)', () => {
  let sourceCode: string;

  beforeAll(() => {
    sourceCode = fs.readFileSync(
      path.join(__dirname, '..', 'components', 'CostDashboard.tsx'),
      'utf-8'
    );
  });

  it('is a client component', () => {
    expect(sourceCode).toMatch(/'use client'/);
  });

  it('fetches from /api/costs', () => {
    expect(sourceCode).toMatch(/\/api\/costs/);
  });

  it('displays total cost', () => {
    expect(sourceCode).toMatch(/Total Cost/i);
  });

  it('displays per-stage breakdown', () => {
    expect(sourceCode).toMatch(/Stage/);
  });

  it('has a refresh button', () => {
    expect(sourceCode).toMatch(/Refresh/);
  });

  it('handles loading state', () => {
    expect(sourceCode).toMatch(/loading/i);
  });

  it('handles error state', () => {
    expect(sourceCode).toMatch(/error/i);
  });

  it('formats cost with dollar sign', () => {
    expect(sourceCode).toMatch(/\$/);
  });

  it('formats tokens with K/M suffixes', () => {
    expect(sourceCode).toMatch(/1_000/);
  });

  it('defines StageCost interface with stage field', () => {
    expect(sourceCode).toMatch(/stage\s*:\s*string/);
  });

  it('defines StageCost interface with totalCost field', () => {
    expect(sourceCode).toMatch(/totalCost\s*:\s*number/);
  });

  it('defines StageCost interface with token fields', () => {
    expect(sourceCode).toMatch(/totalInputTokens\s*:\s*number/);
    expect(sourceCode).toMatch(/totalOutputTokens\s*:\s*number/);
  });

  it('defines StageCost interface with callCount field', () => {
    expect(sourceCode).toMatch(/callCount\s*:\s*number/);
  });

  it('defines CostData interface with byStage array', () => {
    expect(sourceCode).toMatch(/byStage\s*:\s*StageCost\[\]/);
  });

  it('exports CostDashboard as default export', () => {
    expect(sourceCode).toMatch(/export\s+default\s+function\s+CostDashboard/);
  });

  it('displays table headers for Stage, Cost, Input Tokens, Output Tokens, Calls', () => {
    expect(sourceCode).toMatch(/Stage/);
    expect(sourceCode).toMatch(/Cost/);
    expect(sourceCode).toMatch(/Input Tokens/);
    expect(sourceCode).toMatch(/Output Tokens/);
    expect(sourceCode).toMatch(/Calls/);
  });

  it('handles empty byStage array with placeholder message', () => {
    expect(sourceCode).toMatch(/No cost data recorded yet/);
  });

  it('uses useCallback for fetchCosts', () => {
    expect(sourceCode).toMatch(/useCallback/);
  });

  it('disables refresh button while loading', () => {
    expect(sourceCode).toMatch(/disabled=\{loading\}/);
  });

  // Dark theme compliance
  it('uses dark background instead of bg-white', () => {
    expect(sourceCode).not.toMatch(/bg-white/);
    expect(sourceCode).toMatch(/bg-slate-900/);
  });

  it('uses dark-friendly text colors (not text-slate-700/text-slate-600)', () => {
    expect(sourceCode).not.toMatch(/text-slate-700/);
    expect(sourceCode).not.toMatch(/text-slate-600/);
    expect(sourceCode).toMatch(/text-slate-200/);
    expect(sourceCode).toMatch(/text-slate-300/);
  });

  it('uses dark-friendly border colors', () => {
    expect(sourceCode).not.toMatch(/border-slate-200/);
    expect(sourceCode).toMatch(/border-slate-700/);
  });

  it('error message uses dark theme', () => {
    expect(sourceCode).not.toMatch(/bg-red-50/);
    expect(sourceCode).toMatch(/bg-red-900/);
  });
});
