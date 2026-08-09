import React from 'react';
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render } from '@testing-library/react';

// The VpZoomSync component lives inside <ReactFlow> and uses useViewport()
// to keep a CSS custom property --vp-zoom in sync with the viewport zoom.
// This is the correct mechanism because:
//   - onMove only fires on user interaction, not fitView or programmatic changes
//   - useViewport() inside the ReactFlow context is always reactive

let mockZoom = 1;

vi.mock('reactflow', () => ({
  useViewport: () => ({ x: 0, y: 0, zoom: mockZoom }),
}));

// Import after mocking
import { VpZoomSync } from '../components/DependencyViewer';

describe('VpZoomSync', () => {
  let containerDiv: HTMLDivElement;

  beforeEach(() => {
    containerDiv = document.createElement('div');
    document.body.appendChild(containerDiv);
  });

  it('sets --vp-zoom on the target element to the current viewport zoom', () => {
    mockZoom = 0.4;
    render(<VpZoomSync target={containerDiv} />);
    expect(containerDiv.style.getPropertyValue('--vp-zoom')).toBe('0.4');
  });

  it('updates --vp-zoom when zoom changes', () => {
    mockZoom = 0.5;
    const { rerender } = render(<VpZoomSync target={containerDiv} />);
    expect(containerDiv.style.getPropertyValue('--vp-zoom')).toBe('0.5');

    mockZoom = 0.3;
    rerender(<VpZoomSync target={containerDiv} />);
    expect(containerDiv.style.getPropertyValue('--vp-zoom')).toBe('0.3');
  });

  it('sets --vp-zoom on fitView initial zoom (not just user interaction)', () => {
    // Simulate fitView zooming to 0.25 on initial load
    mockZoom = 0.25;
    render(<VpZoomSync target={containerDiv} />);
    expect(containerDiv.style.getPropertyValue('--vp-zoom')).toBe('0.25');
  });

  it('renders nothing visible', () => {
    mockZoom = 1;
    const { container } = render(<VpZoomSync target={containerDiv} />);
    expect(container.firstChild).toBeNull();
  });
});
