import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  TRIANGLE_VERTICES,
  EDGE_WIDTH,
  EDGE_COLOR,
  EDGE_OPACITY_START,
  EDGE_OPACITY_END,
  EDGE_GLOW_1_BLUR,
  EDGE_GLOW_1_OPACITY,
  EDGE_GLOW_2_BLUR,
  EDGE_GLOW_2_OPACITY,
  REIGNITE_EDGE_DURATION,
  GLOW_APPEAR_DURATION,
} from './constants';

export const TriangleEdges: React.FC = () => {
  const frame = useCurrentFrame();

  // Edge opacity reignites from ghost to full
  const edgeOpacity = interpolate(
    frame,
    [0, REIGNITE_EDGE_DURATION],
    [EDGE_OPACITY_START, EDGE_OPACITY_END],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Glow layers fade in
  const glow1Opacity = interpolate(
    frame,
    [0, GLOW_APPEAR_DURATION],
    [0, EDGE_GLOW_1_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const glow2Opacity = interpolate(
    frame,
    [0, GLOW_APPEAR_DURATION],
    [0, EDGE_GLOW_2_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const pathD = `M ${TRIANGLE_VERTICES[0][0]} ${TRIANGLE_VERTICES[0][1]} L ${TRIANGLE_VERTICES[1][0]} ${TRIANGLE_VERTICES[1][1]} L ${TRIANGLE_VERTICES[2][0]} ${TRIANGLE_VERTICES[2][1]} Z`;

  return (
    <g>
      {/* Glow layer 2 (wider, dimmer) */}
      <defs>
        <filter id="edge-glow-2" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation={EDGE_GLOW_2_BLUR / 2} />
        </filter>
      </defs>
      <path
        d={pathD}
        fill="none"
        stroke={EDGE_COLOR}
        strokeWidth={EDGE_WIDTH + 4}
        opacity={glow2Opacity}
        filter="url(#edge-glow-2)"
      />

      {/* Glow layer 1 (tighter, brighter) */}
      <defs>
        <filter id="edge-glow-1" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation={EDGE_GLOW_1_BLUR / 2} />
        </filter>
      </defs>
      <path
        d={pathD}
        fill="none"
        stroke={EDGE_COLOR}
        strokeWidth={EDGE_WIDTH + 2}
        opacity={glow1Opacity}
        filter="url(#edge-glow-1)"
      />

      {/* Main edge stroke */}
      <path
        d={pathD}
        fill="none"
        stroke={EDGE_COLOR}
        strokeWidth={EDGE_WIDTH}
        strokeLinejoin="round"
        opacity={edgeOpacity}
      />
    </g>
  );
};
