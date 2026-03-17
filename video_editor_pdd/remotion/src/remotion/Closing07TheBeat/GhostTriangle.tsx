import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TRIANGLE_VERTICES,
  EDGE_COLOR,
  EDGE_OPACITY_START,
  EDGE_OPACITY_END,
  EDGE_WIDTH_START,
  EDGE_WIDTH_END,
  NODE_COLORS,
  NODE_RADIUS_START,
  NODE_RADIUS_END,
  NODE_OPACITY_START,
  NODE_OPACITY_END,
  GHOST_FADE_DURATION,
  NODE_SHRINK_DURATION,
  WIDTH,
  HEIGHT,
} from './constants';

export const GhostTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Edge animation: fade from luminous to ghost over 30 frames
  const edgeOpacity = interpolate(frame, [0, GHOST_FADE_DURATION], [EDGE_OPACITY_START, EDGE_OPACITY_END], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const edgeWidth = interpolate(frame, [0, GHOST_FADE_DURATION], [EDGE_WIDTH_START, EDGE_WIDTH_END], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  // Node animation: shrink and fade over 25 frames
  const nodeRadius = interpolate(frame, [0, NODE_SHRINK_DURATION], [NODE_RADIUS_START, NODE_RADIUS_END], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const nodeOpacity = interpolate(frame, [0, NODE_SHRINK_DURATION], [NODE_OPACITY_START, NODE_OPACITY_END], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const [[x0, y0], [x1, y1], [x2, y2]] = TRIANGLE_VERTICES;
  const trianglePath = `M ${x0} ${y0} L ${x1} ${y1} L ${x2} ${y2} Z`;

  const nodeColors = [NODE_COLORS.PROMPT, NODE_COLORS.TESTS, NODE_COLORS.GROUNDING];

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
      }}
    >
      {/* Triangle edges */}
      <path
        d={trianglePath}
        fill="none"
        stroke={EDGE_COLOR}
        strokeWidth={edgeWidth}
        opacity={edgeOpacity}
      />

      {/* Nodes at each vertex */}
      {TRIANGLE_VERTICES.map(([cx, cy], i) => (
        <circle
          key={i}
          cx={cx}
          cy={cy}
          r={nodeRadius}
          fill={nodeColors[i]}
          opacity={nodeOpacity}
        />
      ))}
    </svg>
  );
};

export default GhostTriangle;
