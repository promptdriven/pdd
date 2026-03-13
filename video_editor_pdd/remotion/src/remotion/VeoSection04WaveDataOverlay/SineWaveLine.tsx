import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION, CHART, WAVE_DATA, type WaveOverlayLayout } from './constants';

/**
 * Builds an SVG path string from the wave data, mapping data coordinates
 * to pixel positions within the chart area.
 */
const buildWavePath = (layout: WaveOverlayLayout): string => {
  const chartWidth = layout.chart.right - layout.chart.left;
  const chartHeight = layout.chart.bottom - layout.chart.top;

  const points = WAVE_DATA.map((d) => {
    const xNorm = (d.time - CHART.xMin) / (CHART.xMax - CHART.xMin);
    const yNorm = (d.height - CHART.yMin) / (CHART.yMax - CHART.yMin);
    const px = layout.chart.left + xNorm * chartWidth;
    const py = layout.chart.bottom - yNorm * chartHeight;
    return { x: px, y: py };
  });

  // Build a smooth curve using cubic bezier (catmull-rom style)
  let path = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cpx = (prev.x + curr.x) / 2;
    path += ` C ${cpx} ${prev.y}, ${cpx} ${curr.y}, ${curr.x} ${curr.y}`;
  }

  return path;
};

/**
 * Builds a closed SVG path for the filled area under the wave curve.
 */
const buildFillPath = (layout: WaveOverlayLayout): string => {
  const chartWidth = layout.chart.right - layout.chart.left;
  const chartHeight = layout.chart.bottom - layout.chart.top;

  const points = WAVE_DATA.map((d) => {
    const xNorm = (d.time - CHART.xMin) / (CHART.xMax - CHART.xMin);
    const yNorm = (d.height - CHART.yMin) / (CHART.yMax - CHART.yMin);
    const px = layout.chart.left + xNorm * chartWidth;
    const py = layout.chart.bottom - yNorm * chartHeight;
    return { x: px, y: py };
  });

  // Zero line in pixel space
  const zeroNorm = (0 - CHART.yMin) / (CHART.yMax - CHART.yMin);
  const zeroY = layout.chart.bottom - zeroNorm * chartHeight;

  let path = `M ${points[0].x} ${zeroY}`;
  path += ` L ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cpx = (prev.x + curr.x) / 2;
    path += ` C ${cpx} ${prev.y}, ${cpx} ${curr.y}, ${curr.x} ${curr.y}`;
  }
  path += ` L ${points[points.length - 1].x} ${zeroY}`;
  path += ' Z';

  return path;
};

export const SineWaveLine: React.FC<{ layout: WaveOverlayLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Linear draw progress from frame 8 to 28
  const drawProgress = interpolate(
    frame,
    [ANIMATION.waveDrawStart, ANIMATION.waveDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const wavePath = buildWavePath(layout);
  const fillPath = buildFillPath(layout);

  // Estimate total path length for strokeDashoffset animation
  const estimatedPathLength = 2400;
  const dashOffset = estimatedPathLength * (1 - drawProgress);

  // Clip the fill area to only show behind the drawn portion
  const chartWidth = layout.chart.right - layout.chart.left;
  const revealWidth = chartWidth * drawProgress;

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: layout.width,
        height: layout.height,
      }}
    >
      <defs>
        <linearGradient id="waveFillGradient" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={COLORS.chartLine} stopOpacity={0.3} />
          <stop offset="100%" stopColor={COLORS.chartLine} stopOpacity={0} />
        </linearGradient>
        <clipPath id="waveRevealClip">
          <rect
            x={layout.chart.left}
            y={0}
            width={revealWidth}
            height={layout.height}
          />
        </clipPath>
        <filter id="lineGlow">
          <feDropShadow dx="0" dy="0" stdDeviation="8" floodColor={COLORS.chartLine} floodOpacity="0.6" />
        </filter>
      </defs>

      {/* Gradient fill under curve, clipped to revealed portion */}
      <path
        d={fillPath}
        fill="url(#waveFillGradient)"
        clipPath="url(#waveRevealClip)"
      />

      {/* Animated wave line with glow */}
      <path
        d={wavePath}
        fill="none"
        stroke={COLORS.chartLine}
        strokeWidth={CHART.strokeWidth}
        strokeDasharray={estimatedPathLength}
        strokeDashoffset={dashOffset}
        filter="url(#lineGlow)"
        strokeLinecap="round"
      />
    </svg>
  );
};
