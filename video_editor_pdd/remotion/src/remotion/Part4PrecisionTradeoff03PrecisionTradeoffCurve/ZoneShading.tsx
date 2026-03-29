import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  AMBER_ZONE,
  BLUE_ZONE,
  ZONE_OPACITY,
  ZONE_TRANSITION_X,
  CURVE_DATA,
  CURVE_DURATION,
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  CHART_TOP,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
} from "./constants";

function dataToPixelX(dataX: number): number {
  return CHART_LEFT + ((dataX - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

function dataToPixelY(dataY: number): number {
  return CHART_BOTTOM - ((dataY - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

function interpolateY(dataX: number): number {
  for (let j = 0; j < CURVE_DATA.length - 1; j++) {
    if (dataX >= CURVE_DATA[j].x && dataX <= CURVE_DATA[j + 1].x) {
      const t =
        (dataX - CURVE_DATA[j].x) / (CURVE_DATA[j + 1].x - CURVE_DATA[j].x);
      return CURVE_DATA[j].y + t * (CURVE_DATA[j + 1].y - CURVE_DATA[j].y);
    }
  }
  return CURVE_DATA[CURVE_DATA.length - 1].y;
}

export const ZoneShading: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [0, CURVE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.bezier(0.42, 0, 0.58, 1),
  });

  const transitionPx = dataToPixelX(ZONE_TRANSITION_X);

  // Build filled area polygon points — from left to current draw position,
  // following the curve down, then along the x-axis back.
  const maxDataX = X_MIN + drawProgress * (X_MAX - X_MIN);

  const curvePoints = useMemo(() => {
    const pts: string[] = [];
    const steps = 100;
    for (let i = 0; i <= steps; i++) {
      const dx = X_MIN + (i / steps) * (X_MAX - X_MIN);
      const px = dataToPixelX(dx);
      const py = dataToPixelY(interpolateY(dx));
      pts.push(`${px},${py}`);
    }
    return pts;
  }, []);

  // Clip the polygon to the current draw progress
  const visibleSteps = Math.floor(drawProgress * 100);
  const visiblePoints = curvePoints.slice(0, visibleSteps + 1);

  if (visiblePoints.length < 2) return null;

  // Close the polygon along the bottom
  const firstX = dataToPixelX(X_MIN);
  const lastVisibleX = dataToPixelX(
    X_MIN + (visibleSteps / 100) * (X_MAX - X_MIN)
  );

  const amberPolygon =
    visiblePoints.join(" ") +
    ` ${lastVisibleX},${CHART_BOTTOM} ${firstX},${CHART_BOTTOM}`;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <clipPath id="chart-clip">
            <rect
              x={CHART_LEFT}
              y={CHART_TOP}
              width={CHART_WIDTH}
              height={CHART_HEIGHT}
            />
          </clipPath>
          {/* Amber zone: left side */}
          <clipPath id="left-zone">
            <rect
              x={CHART_LEFT}
              y={CHART_TOP}
              width={transitionPx - CHART_LEFT}
              height={CHART_HEIGHT}
            />
          </clipPath>
          {/* Blue zone: right side */}
          <clipPath id="right-zone">
            <rect
              x={transitionPx}
              y={CHART_TOP}
              width={CHART_LEFT + CHART_WIDTH - transitionPx}
              height={CHART_HEIGHT}
            />
          </clipPath>
        </defs>

        {/* Amber shading (left half) */}
        <polygon
          points={amberPolygon}
          fill={AMBER_ZONE}
          opacity={ZONE_OPACITY}
          clipPath="url(#left-zone)"
        />

        {/* Blue shading (right half) */}
        <polygon
          points={amberPolygon}
          fill={BLUE_ZONE}
          opacity={ZONE_OPACITY}
          clipPath="url(#right-zone)"
        />
      </svg>
    </AbsoluteFill>
  );
};
