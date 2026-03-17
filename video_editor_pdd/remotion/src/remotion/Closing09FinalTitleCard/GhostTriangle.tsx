import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TRIANGLE_VERTICES,
  TRIANGLE_EDGE_COLOR,
  TRIANGLE_EDGE_OPACITY,
  TRIANGLE_EDGE_WIDTH,
  TRIANGLE_NODE_RADIUS,
  TRIANGLE_NODE_COLORS,
  TRIANGLE_NODE_OPACITY,
  GHOST_FADE_END,
} from './constants';

/**
 * Ghost triangle watermark — fades from a more visible state to
 * near-invisible ghost over frames 0-30, then holds as a subtle watermark.
 */
export const GhostTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade from slightly visible (0.15 edge / 0.08 node) down to ghost
  const fadeProgress = interpolate(frame, [0, GHOST_FADE_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const edgeOpacity = interpolate(fadeProgress, [0, 1], [0.15, TRIANGLE_EDGE_OPACITY]);
  const nodeOpacity = interpolate(fadeProgress, [0, 1], [0.08, TRIANGLE_NODE_OPACITY]);

  const [top, bottomLeft, bottomRight] = TRIANGLE_VERTICES;

  const pathD = `M ${top[0]} ${top[1]} L ${bottomLeft[0]} ${bottomLeft[1]} L ${bottomRight[0]} ${bottomRight[1]} Z`;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Triangle edges */}
      <path
        d={pathD}
        fill="none"
        stroke={TRIANGLE_EDGE_COLOR}
        strokeWidth={TRIANGLE_EDGE_WIDTH}
        opacity={edgeOpacity}
      />

      {/* Node circles */}
      {TRIANGLE_VERTICES.map((vertex, i) => (
        <circle
          key={i}
          cx={vertex[0]}
          cy={vertex[1]}
          r={TRIANGLE_NODE_RADIUS}
          fill={TRIANGLE_NODE_COLORS[i]}
          opacity={nodeOpacity}
        />
      ))}
    </svg>
  );
};

export default GhostTriangle;
