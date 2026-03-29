import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  DOT_COLOR,
  DOT_RADIUS,
  GLOW_RADIUS,
  GLOW_OPACITY,
  CURVE_DATA,
  DOT_TRAVERSE_DURATION,
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
} from "./constants";

function dataToPixel(
  dataX: number,
  dataY: number
): { px: number; py: number } {
  const px = CHART_LEFT + ((dataX - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
  const py =
    CHART_BOTTOM - ((dataY - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
  return { px, py };
}

function interpolateYFromData(dataX: number): number {
  if (dataX <= CURVE_DATA[0].x) return CURVE_DATA[0].y;
  if (dataX >= CURVE_DATA[CURVE_DATA.length - 1].x)
    return CURVE_DATA[CURVE_DATA.length - 1].y;
  for (let j = 0; j < CURVE_DATA.length - 1; j++) {
    if (dataX >= CURVE_DATA[j].x && dataX <= CURVE_DATA[j + 1].x) {
      const t =
        (dataX - CURVE_DATA[j].x) / (CURVE_DATA[j + 1].x - CURVE_DATA[j].x);
      return CURVE_DATA[j].y + t * (CURVE_DATA[j + 1].y - CURVE_DATA[j].y);
    }
  }
  return CURVE_DATA[CURVE_DATA.length - 1].y;
}

interface TraversingDotProps {
  /** Frame offset within the Sequence (frame 0 = dot appears at left) */
  startDelay?: number;
}

export const TraversingDot: React.FC<TraversingDotProps> = ({
  startDelay = 0,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startDelay;

  // Dot appears immediately at the left extreme (x ≈ 2)
  const dotAppearOpacity = interpolate(localFrame, [0, 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Dot starts traversing at frame 60 (relative to DOT_APPEAR_FRAME=180, so frame 240 absolute)
  const traverseStart = 60; // 240 - 180
  const traverseProgress = interpolate(
    localFrame,
    [traverseStart, traverseStart + DOT_TRAVERSE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.bezier(0.42, 0, 0.58, 1),
    }
  );

  // Map progress to data x: start at x=2 (left extreme), end at x=48 (right extreme)
  const startX = 2;
  const endX = 48;
  const currentDataX = startX + traverseProgress * (endX - startX);
  const currentDataY = interpolateYFromData(currentDataX);
  const { px, py } = dataToPixel(currentDataX, currentDataY);

  if (dotAppearOpacity <= 0) return null;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id="dot-glow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation={GLOW_RADIUS / 2} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Glow */}
        <circle
          cx={px}
          cy={py}
          r={GLOW_RADIUS}
          fill={DOT_COLOR}
          opacity={GLOW_OPACITY * dotAppearOpacity}
        />

        {/* Dot */}
        <circle
          cx={px}
          cy={py}
          r={DOT_RADIUS}
          fill={DOT_COLOR}
          opacity={dotAppearOpacity}
          filter="url(#dot-glow)"
        />
      </svg>
    </AbsoluteFill>
  );
};
