import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CURVE_COLOR,
  CURVE_DATA,
  CURVE_DURATION,
  CHART_LEFT,
  CHART_TOP,
  CHART_RIGHT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
} from "./constants";

/** Convert data-space coords to pixel coords */
function dataToPixel(
  dataX: number,
  dataY: number
): { px: number; py: number } {
  const px = CHART_LEFT + ((dataX - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
  const py = CHART_BOTTOM - ((dataY - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
  return { px, py };
}

/**
 * Build a smooth SVG path through the data points using monotone cubic interpolation.
 * Returns an array of {px, py} pixel points sampled at high resolution for use by other components.
 */
function buildSmoothPath(
  data: { x: number; y: number }[]
): { pathD: string; samples: { px: number; py: number }[] } {
  const pixels = data.map((d) => dataToPixel(d.x, d.y));

  // Catmull-Rom to cubic Bezier
  const n = pixels.length;
  let d = `M ${pixels[0].px},${pixels[0].py}`;

  for (let i = 0; i < n - 1; i++) {
    const p0 = pixels[Math.max(0, i - 1)];
    const p1 = pixels[i];
    const p2 = pixels[i + 1];
    const p3 = pixels[Math.min(n - 1, i + 2)];

    const tension = 6;
    const cp1x = p1.px + (p2.px - p0.px) / tension;
    const cp1y = p1.py + (p2.py - p0.py) / tension;
    const cp2x = p2.px - (p3.px - p1.px) / tension;
    const cp2y = p2.py - (p3.py - p1.py) / tension;

    d += ` C ${cp1x},${cp1y} ${cp2x},${cp2y} ${p2.px},${p2.py}`;
  }

  // Sample the path at high resolution for dot traversal
  const sampleCount = 500;
  const samples: { px: number; py: number }[] = [];
  for (let s = 0; s <= sampleCount; s++) {
    const t = s / sampleCount;
    const dataX = X_MIN + t * (X_MAX - X_MIN);
    // Interpolate y from data using linear interpolation between data points
    let dataY = data[0].y;
    for (let j = 0; j < data.length - 1; j++) {
      if (dataX >= data[j].x && dataX <= data[j + 1].x) {
        const segT =
          (dataX - data[j].x) / (data[j + 1].x - data[j].x);
        dataY = data[j].y + segT * (data[j + 1].y - data[j].y);
        break;
      }
      if (dataX > data[data.length - 1].x) {
        dataY = data[data.length - 1].y;
      }
    }
    const { px, py } = dataToPixel(dataX, dataY);
    samples.push({ px, py });
  }

  return { pathD: d, samples };
}

export const AnimatedCurve: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [0, CURVE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.bezier(0.42, 0, 0.58, 1),
  });

  const { pathD } = useMemo(() => buildSmoothPath(CURVE_DATA), []);

  // Estimate total path length for dash animation (~2000px is typical)
  const pathLength = 2200;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <path
          d={pathD}
          fill="none"
          stroke={CURVE_COLOR}
          strokeWidth={3}
          strokeLinecap="round"
          strokeDasharray={pathLength}
          strokeDashoffset={pathLength * (1 - drawProgress)}
        />
      </svg>
    </AbsoluteFill>
  );
};

/** Export utility for other components to get pixel coordinates along the curve */
export function getCurvePixelSamples(): { px: number; py: number }[] {
  return buildSmoothPath(CURVE_DATA).samples;
}

export { dataToPixel };
