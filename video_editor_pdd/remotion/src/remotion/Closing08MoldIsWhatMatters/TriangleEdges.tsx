// TriangleEdges.tsx — Glowing triangle edges that reignite
import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  TRIANGLE_VERTICES,
  EDGE_COLOR,
  EDGE_WIDTH,
  EDGE_OPACITY_START,
  EDGE_OPACITY_END,
  EDGE_REIGNITE_DURATION,
  GLOW_1_BLUR,
  GLOW_1_OPACITY,
  GLOW_2_BLUR,
  GLOW_2_OPACITY,
  GLOW_APPEAR_DURATION,
} from './constants';

export const TriangleEdges: React.FC = () => {
  const frame = useCurrentFrame();

  // Edge opacity: 0.08 → 0.7 over 15 frames, easeOut(cubic)
  const edgeOpacity = interpolate(
    frame,
    [0, EDGE_REIGNITE_DURATION],
    [EDGE_OPACITY_START, EDGE_OPACITY_END],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // Glow layers fade in over 20 frames
  const glowProgress = interpolate(
    frame,
    [0, GLOW_APPEAR_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    }
  );

  const [[x1, y1], [x2, y2], [x3, y3]] = TRIANGLE_VERTICES;
  const pathD = `M ${x1} ${y1} L ${x2} ${y2} L ${x3} ${y3} Z`;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: WIDTH,
        height: HEIGHT,
        pointerEvents: 'none',
      }}
    >
      <svg width={WIDTH} height={HEIGHT} viewBox={`0 0 ${WIDTH} ${HEIGHT}`}>
        <defs>
          <filter id="glow1" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation={GLOW_1_BLUR / 2} result="blur1" />
          </filter>
          <filter id="glow2" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation={GLOW_2_BLUR / 2} result="blur2" />
          </filter>
        </defs>

        {/* Glow layer 2 — broadest, subtlest */}
        <path
          d={pathD}
          fill="none"
          stroke={EDGE_COLOR}
          strokeWidth={EDGE_WIDTH + 4}
          opacity={GLOW_2_OPACITY * glowProgress}
          filter="url(#glow2)"
        />

        {/* Glow layer 1 — tighter glow */}
        <path
          d={pathD}
          fill="none"
          stroke={EDGE_COLOR}
          strokeWidth={EDGE_WIDTH + 2}
          opacity={GLOW_1_OPACITY * glowProgress}
          filter="url(#glow1)"
        />

        {/* Main edge stroke */}
        <path
          d={pathD}
          fill="none"
          stroke={EDGE_COLOR}
          strokeWidth={EDGE_WIDTH}
          opacity={edgeOpacity}
          strokeLinejoin="round"
        />
      </svg>
    </div>
  );
};

export default TriangleEdges;
