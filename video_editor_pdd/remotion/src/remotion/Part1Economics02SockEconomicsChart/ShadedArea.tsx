import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  DataPoint,
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  CROSSING_POINT,
  LABOR_COST_DATA,
  SOCK_COST_DATA,
  SHADING_START,
  SHADING_FADE_DURATION,
  LINES_START,
  LINES_DRAW_DURATION,
  IRRATIONAL_LABEL_START,
  IRRATIONAL_LABEL_FADE,
  BLUE,
  SHADED_AREA_OPACITY,
  LABEL_COLOR,
  ANNOTATION_OPACITY,
  FONT_FAMILY,
} from './constants';

const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

const yToPixel = (y: number): number =>
  MARGIN_TOP + ((Y_MAX - y) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

/** Linearly interpolate between data points at a given x */
const interpolateData = (data: DataPoint[], x: number): number => {
  if (x <= data[0].x) return data[0].y;
  if (x >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    const a = data[i];
    const b = data[i + 1];
    if (x >= a.x && x <= b.x) {
      const t = (x - a.x) / (b.x - a.x);
      return a.y + t * (b.y - a.y);
    }
  }
  return data[data.length - 1].y;
};

export const ShadedArea: React.FC = () => {
  const frame = useCurrentFrame();

  // Shading opacity fade in
  const shadeFade = interpolate(
    frame,
    [SHADING_START, SHADING_START + SHADING_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) },
  );

  // How far the lines have drawn (determines right edge of shading)
  const drawProgress = interpolate(
    frame,
    [LINES_START, LINES_START + LINES_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const currentX = X_MIN + (X_MAX - X_MIN) * drawProgress;
  const shadeRight = Math.min(currentX, X_MAX);

  // "Darning is irrational" label
  const irrationalOpacity = interpolate(
    frame,
    [IRRATIONAL_LABEL_START, IRRATIONAL_LABEL_START + IRRATIONAL_LABEL_FADE],
    [0, ANNOTATION_OPACITY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) },
  );

  if (shadeFade <= 0 || shadeRight <= CROSSING_POINT.x) return null;

  // Build polygon: upper boundary = labor cost, lower boundary = sock cost
  // After crossing, labor cost > sock cost, so labor is on top (higher y-value)
  // But in pixel space, higher y-value = lower on screen
  const step = 0.5;
  const upperPoints: string[] = []; // labor cost (higher value = top of shaded region)
  const lowerPoints: string[] = []; // sock cost (lower value = bottom of shaded region)

  for (let x = CROSSING_POINT.x; x <= shadeRight; x += step) {
    const laborY = interpolateData(LABOR_COST_DATA, x);
    const sockY = interpolateData(SOCK_COST_DATA, x);
    upperPoints.push(`${xToPixel(x)},${yToPixel(laborY)}`);
    lowerPoints.push(`${xToPixel(x)},${yToPixel(sockY)}`);
  }
  // Include exact endpoint
  {
    const laborY = interpolateData(LABOR_COST_DATA, shadeRight);
    const sockY = interpolateData(SOCK_COST_DATA, shadeRight);
    upperPoints.push(`${xToPixel(shadeRight)},${yToPixel(laborY)}`);
    lowerPoints.push(`${xToPixel(shadeRight)},${yToPixel(sockY)}`);
  }

  // Polygon: upper left → upper right → lower right → lower left
  const polygonPoints = [...upperPoints, ...lowerPoints.reverse()].join(' ');

  // Label center: midpoint between the two lines around x ≈ 1969
  const labelX = CROSSING_POINT.x + (shadeRight - CROSSING_POINT.x) * 0.55;
  const laborAtLabel = interpolateData(LABOR_COST_DATA, labelX);
  const sockAtLabel = interpolateData(SOCK_COST_DATA, labelX);
  const labelDataY = (laborAtLabel + sockAtLabel) / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <polygon
        points={polygonPoints}
        fill={BLUE}
        fillOpacity={SHADED_AREA_OPACITY * shadeFade}
      />

      {irrationalOpacity > 0.01 && (
        <text
          x={xToPixel(labelX)}
          y={yToPixel(labelDataY)}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fillOpacity={irrationalOpacity}
          fontFamily={FONT_FAMILY}
          fontSize={11}
          fontStyle="italic"
        >
          Darning is irrational
        </text>
      )}
    </svg>
  );
};

export default ShadedArea;
