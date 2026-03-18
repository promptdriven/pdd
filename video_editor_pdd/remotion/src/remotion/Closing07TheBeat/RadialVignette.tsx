import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { VIGNETTE_EDGE_OPACITY, VIGNETTE_EDGE_COLOR } from './constants';

/**
 * Radial vignette overlay that darkens edges.
 * Fades in over frames 20-40 (relative to parent), creating tunnel-vision.
 */
export const RadialVignette: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in from frame 20 to 40 with easeOut(quad)
  const vignetteOpacity = interpolate(frame, [20, 40], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        background: `radial-gradient(ellipse at center, transparent 30%, ${VIGNETTE_EDGE_COLOR} 100%)`,
        opacity: vignetteOpacity * VIGNETTE_EDGE_OPACITY,
        pointerEvents: 'none',
      }}
    />
  );
};

export default RadialVignette;
