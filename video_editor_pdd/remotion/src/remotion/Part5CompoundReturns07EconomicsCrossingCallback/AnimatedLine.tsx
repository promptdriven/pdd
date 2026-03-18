import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';
import {
  CHART_LEFT, CHART_RIGHT, CHART_TOP, CHART_BOTTOM,
  CHART_WIDTH, CHART_HEIGHT,
  Y_MAX,
  MORPH_START, MORPH_DURATION,
} from './constants';

interface DataPoint {
  x: number;
  y: number;
}

interface AnimatedLineProps {
  initialData: [number, number][];
  finalData: [number, number][];
  initialXRange: [number, number];
  finalXRange: [number, number];
  color: string;
  initialLabel: string;
  finalLabel: string;
  labelYOffset?: number;
}

/**
 * Converts data points to SVG coordinates, interpolating between
 * initial and final datasets during the morph phase.
 */
function dataToSvg(
  data: [number, number][],
  xRange: [number, number],
): DataPoint[] {
  return data.map(([x, y]) => ({
    x: CHART_LEFT + ((x - xRange[0]) / (xRange[1] - xRange[0])) * CHART_WIDTH,
    y: CHART_BOTTOM - (y / Y_MAX) * CHART_HEIGHT,
  }));
}

function pointsToPath(points: DataPoint[]): string {
  if (points.length === 0) return '';
  return points
    .map((p, i) => `${i === 0 ? 'M' : 'L'}${p.x.toFixed(1)},${p.y.toFixed(1)}`)
    .join(' ');
}

/**
 * Interpolates between two sets of SVG points.
 * Handles different-length arrays by resampling to the longer count.
 */
function interpolatePoints(
  a: DataPoint[],
  b: DataPoint[],
  t: number,
): DataPoint[] {
  const maxLen = Math.max(a.length, b.length);
  const result: DataPoint[] = [];

  for (let i = 0; i < maxLen; i++) {
    const aIdx = Math.min(Math.floor((i / maxLen) * a.length), a.length - 1);
    const bIdx = Math.min(Math.floor((i / maxLen) * b.length), b.length - 1);
    const pa = a[aIdx];
    const pb = b[bIdx];
    result.push({
      x: pa.x + (pb.x - pa.x) * t,
      y: pa.y + (pb.y - pa.y) * t,
    });
  }
  return result;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  initialData,
  finalData,
  initialXRange,
  finalXRange,
  color,
  initialLabel,
  finalLabel,
  labelYOffset = 0,
}) => {
  const frame = useCurrentFrame();

  const morphProgress = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    {extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.4, 0, 0.2, 1)},
  );

  const initialPoints = dataToSvg(initialData, initialXRange);
  const finalPoints = dataToSvg(finalData, finalXRange);
  const currentPoints = interpolatePoints(initialPoints, finalPoints, morphProgress);

  const pathD = pointsToPath(currentPoints);

  // Label position: at the end of the line
  const lastPoint = currentPoints[currentPoints.length - 1];

  // Label text morph
  const labelOpacity = morphProgress < 0.4
    ? 0.7
    : morphProgress < 0.6
      ? 0.7 * (1 - (morphProgress - 0.4) / 0.2)
      : 0.7;

  const currentLabel = morphProgress < 0.5 ? initialLabel : finalLabel;

  return (
    <svg
      width={1920}
      height={1080}
      style={{position: 'absolute', top: 0, left: 0}}
    >
      {/* The line */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeOpacity={0.85}
      />

      {/* Line label */}
      {lastPoint && (
        <text
          x={Math.min(lastPoint.x + 12, CHART_RIGHT - 10)}
          y={lastPoint.y + labelYOffset}
          fill={color}
          fillOpacity={labelOpacity}
          fontSize={13}
          fontFamily="Inter, sans-serif"
          dominantBaseline="middle"
        >
          {currentLabel}
        </text>
      )}
    </svg>
  );
};

export default AnimatedLine;
