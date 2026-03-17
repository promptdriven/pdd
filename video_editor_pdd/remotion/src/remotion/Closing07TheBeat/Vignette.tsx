import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  VIGNETTE_EDGE_OPACITY,
  VIGNETTE_FADE_START,
  VIGNETTE_FADE_DURATION,
} from './constants';

/**
 * Radial vignette overlay that darkens the edges of the frame,
 * creating a tunnel-vision effect focused on the ghost triangle.
 */
export const Vignette: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [VIGNETTE_FADE_START, VIGNETTE_FADE_START + VIGNETTE_FADE_DURATION],
    [0, VIGNETTE_EDGE_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        background: `radial-gradient(ellipse at center, transparent 30%, rgba(0, 0, 0, ${opacity}) 100%)`,
        pointerEvents: 'none',
      }}
    />
  );
};

export default Vignette;
