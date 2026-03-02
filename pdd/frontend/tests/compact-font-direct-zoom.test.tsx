import React from 'react';
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';

// ModuleNode uses useViewport() to get the current zoom and determine compact
// mode.  The compact-mode label must compute its font-size directly from the
// zoom value (e.g. `${Math.round(14 / zoom)}px`) rather than deferring to a
// CSS custom-property (var(--vp-zoom, 1)).  The CSS-variable approach is
// unreliable because VpZoomSync's useEffect updates --vp-zoom *after* paint,
// leaving compact nodes with the stale fallback value of 1 during the first
// visible frame — and permanently whenever VpZoomSync's target ref is null
// (which happens on the initial render cycle before the container div mounts).

let mockZoom = 1;

vi.mock('reactflow', () => ({
  useViewport: () => ({ x: 0, y: 0, zoom: mockZoom }),
  Handle: ({ type }: { type: string }) =>
    React.createElement('div', { 'data-testid': `handle-${type}` }),
  Position: { Top: 'top', Bottom: 'bottom' },
  memo: (fn: unknown) => fn,
}));

import ModuleNode from '../components/ModuleNode';

const baseData = {
  label: 'auth_service',
  module: {
    filename: 'auth_service',
    filepath: 'src/auth',
    description: 'Handles user authentication',
    dependencies: [],
    priority: 1,
    interface: { type: 'service' },
  },
  hasPrompt: false,
  colors: {
    bg: 'bg-surface-800',
    border: 'border-surface-700',
    hover: 'hover:bg-surface-700',
    text: 'text-surface-400',
  },
};

const renderCompactNode = (zoom: number) => {
  mockZoom = zoom;
  return render(
    React.createElement(ModuleNode as any, {
      id: 'test-node',
      data: baseData,
      selected: false,
      xPos: 0,
      yPos: 0,
      type: 'moduleNode',
      zIndex: 1,
      isConnectable: true,
      dragging: false,
    }),
  );
};

describe('ModuleNode compact mode — font-size uses zoom directly', () => {
  it('at zoom=0.3 the label font-size is Math.round(14/0.3)=47 px', () => {
    renderCompactNode(0.3);
    const label = screen.getByText('auth_service');
    expect(label.style.fontSize).toBe('47px');
  });

  it('at zoom=0.4 the label font-size is Math.round(14/0.4)=35 px', () => {
    renderCompactNode(0.4);
    const label = screen.getByText('auth_service');
    expect(label.style.fontSize).toBe('35px');
  });

  it('at zoom=0.25 the label font-size is Math.round(14/0.25)=56 px', () => {
    renderCompactNode(0.25);
    const label = screen.getByText('auth_service');
    expect(label.style.fontSize).toBe('56px');
  });

  it('does NOT use a CSS variable for the font-size', () => {
    renderCompactNode(0.3);
    const label = screen.getByText('auth_service');
    // The font-size should be an explicit pixel value, not a calc/var expression
    expect(label.style.fontSize).not.toContain('var(');
    expect(label.style.fontSize).not.toContain('calc(');
  });
});
