import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  TRIANGLE_VERTICES,
  TRIANGLE_LINE_COLOR,
  HOLD_START,
  TOTAL_DURATION,
} from './constants';

interface PddTriangleProps {
  triangleOpacity: number;
  glowOpacity: number;
  brightenAtEnd?: boolean;
}

const PddTriangle: React.FC<PddTriangleProps> = ({
  triangleOpacity,
  glowOpacity,
  brightenAtEnd = false,
}) => {
  const frame = useCurrentFrame();

  // Slow pulse on vertex glows
  const pulsePhase = Math.sin((frame / 30) * Math.PI * 0.5);
  const basePulse = 0.85 + 0.15 * pulsePhase;

  // End-of-section brightening
  const brightenFactor = brightenAtEnd
    ? interpolate(frame, [HOLD_START, TOTAL_DURATION], [1, 1.6], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      })
    : 1;

  const effectiveGlow = glowOpacity * basePulse * brightenFactor;
  const effectiveOpacity = triangleOpacity * brightenFactor;

  const verts = TRIANGLE_VERTICES;
  const pathD = `M ${verts[0].x} ${verts[0].y} L ${verts[1].x} ${verts[1].y} L ${verts[2].x} ${verts[2].y} Z`;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        opacity: effectiveOpacity,
      }}
    >
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Triangle edges */}
        <path
          d={pathD}
          fill="none"
          stroke={TRIANGLE_LINE_COLOR}
          strokeWidth={2}
          opacity={0.5}
        />

        {/* Vertex glows and labels */}
        {verts.map((v, i) => (
          <g key={i}>
            <circle cx={v.x} cy={v.y} r={24} fill={v.color} opacity={effectiveGlow} />
            <circle cx={v.x} cy={v.y} r={8} fill={v.color} opacity={effectiveGlow * 2} />
            <text
              x={v.x}
              y={v.y + (i === 0 ? -36 : 44)}
              textAnchor="middle"
              fill={v.color}
              fontSize={14}
              fontFamily="system-ui, sans-serif"
              fontWeight={600}
              opacity={0.6}
            >
              {v.label}
            </text>
          </g>
        ))}
      </svg>
    </div>
  );
};

export default PddTriangle;
