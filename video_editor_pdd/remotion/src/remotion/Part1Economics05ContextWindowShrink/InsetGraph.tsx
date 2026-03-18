import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  INSET_X,
  INSET_Y,
  INSET_WIDTH,
  INSET_HEIGHT,
  COLOR_RED,
  TEXT_MUTED,
  TEXT_LIGHT,
  BLOCK_BORDER,
  PERF_DATA,
} from './constants';

const PADDING = { top: 36, right: 16, bottom: 28, left: 32 };
const CHART_W = INSET_WIDTH - PADDING.left - PADDING.right;
const CHART_H = INSET_HEIGHT - PADDING.top - PADDING.bottom;

export const InsetGraph: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in the entire inset
  const containerOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Draw the line over 30 frames starting at frame 10
  const lineProgress = interpolate(frame, [10, 40], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Label fade in
  const labelOpacity = interpolate(frame, [35, 50], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Build SVG path
  const fullPath = useMemo(() => {
    return PERF_DATA.map((pt, i) => {
      const x = PADDING.left + pt.x * CHART_W;
      const y = PADDING.top + (1 - pt.y / 100) * CHART_H;
      return `${i === 0 ? 'M' : 'L'} ${x} ${y}`;
    }).join(' ');
  }, []);

  // Calculate total path length for stroke-dasharray animation
  const pathLength = useMemo(() => {
    let length = 0;
    for (let i = 1; i < PERF_DATA.length; i++) {
      const x1 = PADDING.left + PERF_DATA[i - 1].x * CHART_W;
      const y1 = PADDING.top + (1 - PERF_DATA[i - 1].y / 100) * CHART_H;
      const x2 = PADDING.left + PERF_DATA[i].x * CHART_W;
      const y2 = PADDING.top + (1 - PERF_DATA[i].y / 100) * CHART_H;
      length += Math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2);
    }
    return length;
  }, []);

  // Y-axis labels
  const yLabels = [0, 50, 100];

  return (
    <div
      style={{
        position: 'absolute',
        left: INSET_X,
        top: INSET_Y,
        width: INSET_WIDTH,
        height: INSET_HEIGHT,
        opacity: containerOpacity,
        border: `1px solid ${BLOCK_BORDER}26`,
        borderRadius: 6,
        backgroundColor: 'rgba(13, 17, 23, 0.9)',
        overflow: 'hidden',
      }}
    >
      {/* Title */}
      <div
        style={{
          position: 'absolute',
          left: PADDING.left,
          top: 10,
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          fontWeight: 'bold',
          color: TEXT_LIGHT,
          opacity: 0.5,
        }}
      >
        Performance vs. Context Length
      </div>

      {/* SVG Chart */}
      <svg width={INSET_WIDTH} height={INSET_HEIGHT} style={{ position: 'absolute', top: 0, left: 0 }}>
        {/* Y-axis gridlines */}
        {yLabels.map((val) => {
          const y = PADDING.top + (1 - val / 100) * CHART_H;
          return (
            <g key={val}>
              <line
                x1={PADDING.left}
                y1={y}
                x2={INSET_WIDTH - PADDING.right}
                y2={y}
                stroke={BLOCK_BORDER}
                strokeWidth={0.5}
                opacity={0.2}
              />
              <text
                x={PADDING.left - 4}
                y={y + 3}
                textAnchor="end"
                fill={TEXT_MUTED}
                fontSize={7}
                fontFamily="Inter, sans-serif"
                opacity={0.3}
              >
                {val}%
              </text>
            </g>
          );
        })}

        {/* X-axis line */}
        <line
          x1={PADDING.left}
          y1={PADDING.top + CHART_H}
          x2={INSET_WIDTH - PADDING.right}
          y2={PADDING.top + CHART_H}
          stroke={BLOCK_BORDER}
          strokeWidth={0.5}
          opacity={0.3}
        />

        {/* Performance decline line */}
        <path
          d={fullPath}
          fill="none"
          stroke={COLOR_RED}
          strokeWidth={2}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={pathLength}
          strokeDashoffset={pathLength * (1 - lineProgress)}
        />
      </svg>

      {/* Range label */}
      <div
        style={{
          position: 'absolute',
          right: PADDING.right + 4,
          top: PADDING.top + 8,
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: COLOR_RED,
          opacity: labelOpacity * 0.6,
          fontWeight: 'bold',
        }}
      >
        −14% to −85%
      </div>

      {/* Citation */}
      <div
        style={{
          position: 'absolute',
          right: PADDING.right + 4,
          bottom: 6,
          fontFamily: 'Inter, sans-serif',
          fontSize: 8,
          color: TEXT_MUTED,
          opacity: labelOpacity * 0.3,
          fontStyle: 'italic',
        }}
      >
        EMNLP, 2025
      </div>
    </div>
  );
};

export default InsetGraph;
