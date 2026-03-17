import React from 'react';
import { useCurrentFrame } from 'remotion';
import {
  VERTICES,
  EDGE_COLOR,
  EDGE_OPACITY,
  EDGE_GLOW_BLUR,
  EDGE_GLOW_OPACITY,
  NODE_BLUE,
  NODE_ORANGE,
  NODE_GREEN,
  NODE_RADIUS,
  NODE_PULSE_MIN,
  NODE_PULSE_MAX,
  NODE_PULSE_PERIOD,
  NODE_LABELS,
} from './constants';

const NODES: { center: [number, number]; color: string }[] = [
  { center: VERTICES[0], color: NODE_BLUE },
  { center: VERTICES[1], color: NODE_ORANGE },
  { center: VERTICES[2], color: NODE_GREEN },
];

export const Triangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Gentle pulse: oscillates between NODE_PULSE_MIN and NODE_PULSE_MAX
  const pulse =
    NODE_PULSE_MIN +
    (NODE_PULSE_MAX - NODE_PULSE_MIN) *
      (0.5 + 0.5 * Math.sin((frame / NODE_PULSE_PERIOD) * Math.PI * 2));

  // Build triangle path
  const pathD = `M ${VERTICES[0][0]} ${VERTICES[0][1]} L ${VERTICES[1][0]} ${VERTICES[1][1]} L ${VERTICES[2][0]} ${VERTICES[2][1]} Z`;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id="edgeGlow">
          <feGaussianBlur stdDeviation={EDGE_GLOW_BLUR} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        {NODES.map((node, i) => (
          <filter key={`nodeGlow${i}`} id={`nodeGlow${i}`}>
            <feGaussianBlur stdDeviation={3} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        ))}
      </defs>

      {/* Triangle edges with glow */}
      <path
        d={pathD}
        fill="none"
        stroke={EDGE_COLOR}
        strokeWidth={2}
        opacity={EDGE_OPACITY}
        filter="url(#edgeGlow)"
      />
      {/* Second pass for glow layer */}
      <path
        d={pathD}
        fill="none"
        stroke={EDGE_COLOR}
        strokeWidth={2}
        opacity={EDGE_GLOW_OPACITY}
        filter="url(#edgeGlow)"
      />

      {/* Node circles */}
      {NODES.map((node, i) => (
        <circle
          key={`node${i}`}
          cx={node.center[0]}
          cy={node.center[1]}
          r={pulse}
          fill={node.color}
          opacity={0.9}
          filter={`url(#nodeGlow${i})`}
        />
      ))}

      {/* Labels */}
      {NODE_LABELS.map((label, i) => (
        <text
          key={`label${i}`}
          x={label.pos[0]}
          y={label.pos[1]}
          fill={label.color}
          fontSize={12}
          fontFamily="sans-serif"
          textAnchor="middle"
          opacity={0.7}
        >
          {label.text}
        </text>
      ))}
    </svg>
  );
};
