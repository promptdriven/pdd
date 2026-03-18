import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TRIANGLE_VERTICES,
  GHOST_EDGE_COLOR,
  GHOST_EDGE_OPACITY,
  GHOST_EDGE_WIDTH,
  LUMINOUS_EDGE_OPACITY,
  LUMINOUS_EDGE_WIDTH,
  GHOST_NODE_RADIUS,
  GHOST_NODE_OPACITY,
  LUMINOUS_NODE_RADIUS,
  LUMINOUS_NODE_OPACITY,
  NODE_PROMPT_COLOR,
  NODE_TESTS_COLOR,
  NODE_GROUNDING_COLOR,
} from './constants';

const NODE_COLORS = [NODE_PROMPT_COLOR, NODE_TESTS_COLOR, NODE_GROUNDING_COLOR];

export const GhostTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Edge transition: luminous → ghost over 30 frames with easeIn(quad)
  const edgeOpacity = interpolate(frame, [0, 30], [LUMINOUS_EDGE_OPACITY, GHOST_EDGE_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const edgeWidth = interpolate(frame, [0, 30], [LUMINOUS_EDGE_WIDTH, GHOST_EDGE_WIDTH], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  // Node shrink over 25 frames with easeIn(quad)
  const nodeRadius = interpolate(frame, [0, 25], [LUMINOUS_NODE_RADIUS, GHOST_NODE_RADIUS], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const nodeOpacity = interpolate(frame, [0, 25], [LUMINOUS_NODE_OPACITY, GHOST_NODE_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  // Glow dissolve over 20 frames
  const glowOpacity = interpolate(frame, [0, 20], [0.4, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const [v0, v1, v2] = TRIANGLE_VERTICES;
  const pathD = `M ${v0[0]} ${v0[1]} L ${v1[0]} ${v1[1]} L ${v2[0]} ${v2[1]} Z`;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Glow layer — dissolves first */}
      {glowOpacity > 0.001 && (
        <defs>
          <filter id="triangleGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="12" result="blur" />
          </filter>
        </defs>
      )}
      {glowOpacity > 0.001 && (
        <path
          d={pathD}
          fill="none"
          stroke={GHOST_EDGE_COLOR}
          strokeWidth={edgeWidth * 3}
          opacity={glowOpacity}
          filter="url(#triangleGlow)"
        />
      )}

      {/* Triangle edges — hairline */}
      <path
        d={pathD}
        fill="none"
        stroke={GHOST_EDGE_COLOR}
        strokeWidth={edgeWidth}
        opacity={edgeOpacity}
      />

      {/* Nodes */}
      {TRIANGLE_VERTICES.map((vertex, i) => (
        <circle
          key={i}
          cx={vertex[0]}
          cy={vertex[1]}
          r={nodeRadius}
          fill={NODE_COLORS[i]}
          opacity={nodeOpacity}
        />
      ))}
    </svg>
  );
};

export default GhostTriangle;
