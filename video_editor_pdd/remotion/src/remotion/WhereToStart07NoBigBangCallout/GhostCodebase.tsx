import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { GHOST_NODES, TIMING } from './constants';

/**
 * Ghost codebase topology — heavily blurred background element.
 * Renders scattered circles representing the codebase topology from the
 * previous shot, fading to a ghostly state over the first 20 frames.
 */
export const GhostCodebase: React.FC = () => {
  const frame = useCurrentFrame();

  // Blur increases and opacity decreases over first 20 frames
  const settleProgress = interpolate(
    frame,
    [TIMING.GHOST_SETTLE_START, TIMING.GHOST_SETTLE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Start at 0.15 opacity, settle to 0.06
  const containerOpacity = interpolate(settleProgress, [0, 1], [0.15, 0.06]);
  // Start at 8px blur, settle to 30px
  const blurRadius = interpolate(settleProgress, [0, 1], [8, 30]);

  return (
    <AbsoluteFill
      style={{
        opacity: containerOpacity,
        filter: `blur(${blurRadius}px)`,
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Edges between some nodes */}
        {GHOST_NODES.map((node, i) => {
          const next = GHOST_NODES[(i + 3) % GHOST_NODES.length];
          return (
            <line
              key={`edge-${i}`}
              x1={node.x}
              y1={node.y}
              x2={next.x}
              y2={next.y}
              stroke="#334155"
              strokeWidth={1}
              opacity={0.3}
            />
          );
        })}
        {/* Nodes */}
        {GHOST_NODES.map((node, i) => (
          <circle
            key={`node-${i}`}
            cx={node.x}
            cy={node.y}
            r={node.r}
            fill={node.color}
            opacity={node.color === '#4A90D9' ? 0.5 : 0.3}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
