import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  VERTICES,
  EDGE_WIDTH,
  EDGE_OPACITY,
  EDGES_START,
  EDGE_DURATION,
} from './constants';

/**
 * Draws the three edges of the triangle in sequence:
 *  edge 0: top → bottom-left   (frames 50-60)
 *  edge 1: bottom-left → bottom-right (frames 60-70)
 *  edge 2: bottom-right → top  (frames 70-80)
 */
const TriangleEdges: React.FC = () => {
  const frame = useCurrentFrame();

  const edges: Array<{ x1: number; y1: number; x2: number; y2: number; delay: number }> = [
    { x1: VERTICES[0].x, y1: VERTICES[0].y, x2: VERTICES[1].x, y2: VERTICES[1].y, delay: 0 },
    { x1: VERTICES[1].x, y1: VERTICES[1].y, x2: VERTICES[2].x, y2: VERTICES[2].y, delay: EDGE_DURATION },
    { x1: VERTICES[2].x, y1: VERTICES[2].y, x2: VERTICES[0].x, y2: VERTICES[0].y, delay: EDGE_DURATION * 2 },
  ];

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
      viewBox="0 0 1920 1080"
    >
      <defs>
        <linearGradient id="edgeGrad" x1="0%" y1="0%" x2="100%" y2="0%">
          <stop offset="0%" stopColor="#334155" />
          <stop offset="100%" stopColor="#4A5568" />
        </linearGradient>
      </defs>
      {edges.map((edge, i) => {
        const edgeStart = EDGES_START + edge.delay;
        const edgeEnd = edgeStart + EDGE_DURATION;
        const progress = interpolate(frame, [edgeStart, edgeEnd], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.cubic),
        });

        const dx = edge.x2 - edge.x1;
        const dy = edge.y2 - edge.y1;
        const length = Math.sqrt(dx * dx + dy * dy);
        const dashOffset = length * (1 - progress);

        return (
          <line
            key={i}
            x1={edge.x1}
            y1={edge.y1}
            x2={edge.x2}
            y2={edge.y2}
            stroke="url(#edgeGrad)"
            strokeWidth={EDGE_WIDTH}
            opacity={EDGE_OPACITY}
            strokeDasharray={length}
            strokeDashoffset={dashOffset}
          />
        );
      })}
    </svg>
  );
};

export default TriangleEdges;
