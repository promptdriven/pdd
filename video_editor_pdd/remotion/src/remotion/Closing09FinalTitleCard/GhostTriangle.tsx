import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  TRIANGLE_VERTICES,
  TRIANGLE_EDGE_COLOR,
  TRIANGLE_EDGE_OPACITY,
  TRIANGLE_EDGE_WIDTH,
  NODE_RADIUS,
  NODE_COLORS,
  NODE_OPACITY,
  GHOST_FADE_DURATION,
} from './constants';

export const GhostTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Triangle fades from slightly more visible to ghost-level over first 25 frames
  // Simulates "previous triangle fading to ghost watermark"
  const fadeProgress = interpolate(frame, [0, GHOST_FADE_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  // Start at slightly higher opacity and settle to ghost level
  const edgeOpacity = interpolate(fadeProgress, [0, 1], [0.15, TRIANGLE_EDGE_OPACITY]);
  const nodeOpacity = interpolate(fadeProgress, [0, 1], [0.08, NODE_OPACITY]);

  const [v0, v1, v2] = TRIANGLE_VERTICES;

  const trianglePath = `M ${v0[0]} ${v0[1]} L ${v1[0]} ${v1[1]} L ${v2[0]} ${v2[1]} Z`;

  return (
    <AbsoluteFill style={{ zIndex: 0 }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Triangle edges */}
        <path
          d={trianglePath}
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
            r={NODE_RADIUS}
            fill={NODE_COLORS[i]}
            opacity={nodeOpacity}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
