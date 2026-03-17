// AnimatedLine.tsx — SVG polyline for a data series with label
import React from 'react';
import { CHART, OPACITIES, Y_RANGE } from './constants';

interface DataPoint {
  x: number;
  y: number;
}

interface AnimatedLineProps {
  /** Array of data points */
  data: DataPoint[];
  /** X-axis range [min, max] for mapping */
  xRange: [number, number];
  /** Line color */
  color: string;
  /** Label text */
  label: string;
  /** Group opacity (for fade-in) */
  opacity: number;
}

/** Maps a data point to SVG pixel coords within the chart area. */
const mapToPixel = (
  pt: DataPoint,
  xRange: [number, number],
): { px: number; py: number } => {
  const { left, top, width, height } = CHART;
  const xFrac = (pt.x - xRange[0]) / (xRange[1] - xRange[0]);
  const yFrac = pt.y / Y_RANGE.max;
  return {
    px: left + xFrac * width,
    py: top + height - yFrac * height,
  };
};

/**
 * Renders an SVG polyline for a data series plus a label positioned
 * near the last data point.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  xRange,
  color,
  label,
  opacity,
}) => {
  const points = data.map((pt) => mapToPixel(pt, xRange));
  const pathD = points
    .map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.px} ${p.py}`)
    .join(' ');

  const lastPt = points[points.length - 1];
  // Label offset: position near end of line
  const labelX = lastPt.px + 10;
  const labelY = lastPt.py;

  return (
    <div style={{ position: 'absolute', inset: 0, opacity }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={2.5}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>
      <div
        style={{
          position: 'absolute',
          left: labelX,
          top: labelY - 8,
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          color,
          opacity: OPACITIES.lineLabel,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default AnimatedLine;
