import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TIMING } from './constants';

/**
 * GhostCodebase renders a blurred, abstract codebase topology
 * as a faint background element. Uses simple SVG shapes to suggest
 * a network of modules with a blue cluster glow.
 */
export const GhostCodebase: React.FC = () => {
  const frame = useCurrentFrame();

  // Ghost fades in from slightly higher opacity to its resting 0.06
  const ghostOpacity = interpolate(
    frame,
    [TIMING.GHOST_START, TIMING.GHOST_END],
    [0.12, 0.06],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Positions for abstract "module" nodes
  const nodes = [
    { x: 400, y: 300, r: 18, color: '#475569' },
    { x: 520, y: 260, r: 14, color: '#475569' },
    { x: 600, y: 340, r: 20, color: '#475569' },
    { x: 480, y: 400, r: 12, color: '#475569' },
    { x: 350, y: 440, r: 16, color: '#475569' },
    { x: 700, y: 280, r: 15, color: '#475569' },
    { x: 750, y: 400, r: 13, color: '#475569' },
    // Blue cluster (converted modules)
    { x: 960, y: 480, r: 22, color: COLORS.GHOST_BLUE },
    { x: 1040, y: 520, r: 18, color: COLORS.GHOST_BLUE },
    { x: 1000, y: 560, r: 16, color: COLORS.GHOST_BLUE },
    { x: 920, y: 540, r: 14, color: COLORS.GHOST_BLUE },
    // More neutral nodes
    { x: 1200, y: 350, r: 17, color: '#475569' },
    { x: 1300, y: 420, r: 14, color: '#475569' },
    { x: 1400, y: 300, r: 19, color: '#475569' },
    { x: 1500, y: 380, r: 12, color: '#475569' },
    { x: 1150, y: 500, r: 15, color: '#475569' },
    { x: 1350, y: 550, r: 11, color: '#475569' },
  ];

  // Edges connecting some nodes
  const edges = [
    [0, 1], [1, 2], [2, 3], [3, 4], [0, 4],
    [1, 5], [5, 6], [2, 6],
    [7, 8], [8, 9], [9, 10], [10, 7],
    [6, 7],
    [11, 12], [12, 13], [13, 14],
    [11, 15], [15, 16], [12, 16],
    [8, 11],
  ];

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
        opacity: ghostOpacity,
        filter: 'blur(30px)',
      }}
    >
      <svg
        width={CANVAS.WIDTH}
        height={CANVAS.HEIGHT}
        viewBox={`0 0 ${CANVAS.WIDTH} ${CANVAS.HEIGHT}`}
      >
        {/* Edges */}
        {edges.map(([from, to], i) => (
          <line
            key={`edge-${i}`}
            x1={nodes[from].x}
            y1={nodes[from].y}
            x2={nodes[to].x}
            y2={nodes[to].y}
            stroke={
              nodes[from].color === COLORS.GHOST_BLUE ||
              nodes[to].color === COLORS.GHOST_BLUE
                ? COLORS.GHOST_BLUE
                : '#334155'
            }
            strokeWidth={2}
            opacity={0.4}
          />
        ))}
        {/* Nodes */}
        {nodes.map((node, i) => (
          <circle
            key={`node-${i}`}
            cx={node.x}
            cy={node.y}
            r={node.r}
            fill={node.color}
            opacity={node.color === COLORS.GHOST_BLUE ? 0.5 : 0.3}
          />
        ))}
        {/* Blue cluster glow */}
        <circle
          cx={980}
          cy={520}
          r={120}
          fill={COLORS.GHOST_BLUE}
          opacity={0.08}
        />
      </svg>
    </div>
  );
};
