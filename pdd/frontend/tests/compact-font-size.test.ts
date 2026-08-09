import { describe, it, expect } from 'vitest';

// getCompactFontPx is a pure math helper: Math.round(14 / zoom).
// React Flow applies transform:scale(zoom) to its viewport container, so a
// font rendered at (14/zoom)px in node-space will always APPEAR as 14px on
// screen regardless of the viewport zoom level.
//
// ModuleNode calls getCompactFontPx(zoom) directly with the zoom value from
// useViewport(), producing an explicit pixel font-size in the inline style.

import { getCompactFontPx } from '../components/DependencyViewer';

describe('getCompactFontPx — mirrors calc(14px / var(--vp-zoom, 1))', () => {
  it('grows larger as zoom decreases so text stays readable on screen', () => {
    expect(getCompactFontPx(0.4)).toBeGreaterThan(getCompactFontPx(0.5));
    expect(getCompactFontPx(0.3)).toBeGreaterThan(getCompactFontPx(0.4));
  });

  it('at zoom=0.5 returns 28px — apparent screen size = 28 × 0.5 = 14px', () => {
    expect(getCompactFontPx(0.5)).toBe(28);
  });

  it('at zoom=0.25 returns 56px — apparent screen size = 56 × 0.25 = 14px', () => {
    expect(getCompactFontPx(0.25)).toBe(56);
  });

  it('maintains constant ~14px apparent size: fontPx × zoom ≈ 14 for any zoom', () => {
    for (const zoom of [0.5, 0.4, 0.3, 0.2]) {
      expect(getCompactFontPx(zoom) * zoom).toBeCloseTo(14, 0);
    }
  });

  it('doubles font size when zoom halves (inverse proportional)', () => {
    expect(getCompactFontPx(0.25)).toBeCloseTo(getCompactFontPx(0.5) * 2, 0);
  });
});
