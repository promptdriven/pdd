// TriangleFrame.tsx — Persistent PDD triangle with glowing edges and pulsing nodes
import React from 'react';
import { useCurrentFrame } from 'remotion';
import {
  TRIANGLE,
  NODES,
  NODE_RADIUS,
  NODE_PULSE_MIN,
  NODE_PULSE_MAX,
  NODE_PULSE_PERIOD,
} from './constants';

export const TriangleFrame: React.FC = () => {
  const frame = useCurrentFrame();

  const [[x0, y0], [x1, y1], [x2, y2]] = TRIANGLE.vertices;
  const pathD = `M ${x0} ${y0} L ${x1} ${y1} L ${x2} ${y2} Z`;

  // Gentle node radius pulse
  const pulseT = (Math.sin((frame / NODE_PULSE_PERIOD) * Math.PI * 2) + 1) / 2;
  const r = NODE_PULSE_MIN + (NODE_PULSE_MAX - NODE_PULSE_MIN) * pulseT;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Edge glow */}
      <defs>
        <filter id="edgeGlow">
          <feGaussianBlur stdDeviation={TRIANGLE.glowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        {/* Node glow filters */}
        {NODES.map((node, i) => (
          <filter key={i} id={`nodeGlow${i}`}>
            <feGaussianBlur stdDeviation={6} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        ))}
      </defs>

      {/* Triangle edges */}
      <path
        d={pathD}
        fill="none"
        stroke={TRIANGLE.edgeColor}
        strokeWidth={TRIANGLE.edgeWidth}
        opacity={TRIANGLE.edgeOpacity}
        filter="url(#edgeGlow)"
      />

      {/* Nodes */}
      {NODES.map((node, i) => (
        <g key={i}>
          {/* Outer glow */}
          <circle
            cx={node.center[0]}
            cy={node.center[1]}
            r={r + 4}
            fill={node.fill}
            opacity={0.15}
            filter={`url(#nodeGlow${i})`}
          />
          {/* Solid node */}
          <circle
            cx={node.center[0]}
            cy={node.center[1]}
            r={r}
            fill={node.fill}
            opacity={0.9}
          />
          {/* Label */}
          <text
            x={node.center[0]}
            y={
              node.center[1] +
              (i === 0 ? -35 : 45)
            }
            textAnchor="middle"
            fontFamily="JetBrains Mono, monospace"
            fontSize={12}
            fill={node.fill}
            opacity={0.5}
          >
            {node.label}
          </text>
        </g>
      ))}
    </svg>
  );
};
