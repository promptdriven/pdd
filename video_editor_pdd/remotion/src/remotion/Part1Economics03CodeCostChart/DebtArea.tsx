import React, { useMemo } from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  DEBT_FILL_COLOR,
  DEBT_FILL_OPACITY,
  TOTAL_COST_DEBT_DATA,
  IMMEDIATE_PATCH_DATA,
  DASHED_LINE_START,
  DASHED_LINE_END,
  PULLBACK_START,
  PULLBACK_END,
  mapX,
  mapY,
} from "./constants";

export const DebtArea: React.FC = () => {
  const frame = useCurrentFrame();

  // Build polygon points from the two data series
  const polygonPoints = useMemo(() => {
    // Upper boundary: total cost (dashed)
    const upper = TOTAL_COST_DEBT_DATA.map(
      (pt) => `${mapX(pt.x)},${mapY(pt.y)}`
    ).join(" ");
    // Lower boundary: immediate patch (reversed for polygon closure)
    const lower = [...IMMEDIATE_PATCH_DATA]
      .reverse()
      .map((pt) => `${mapX(pt.x)},${mapY(pt.y)}`)
      .join(" ");
    return `${upper} ${lower}`;
  }, []);

  // Debt area fades in when dashed line draws
  const fillOpacity = interpolate(
    frame,
    [DASHED_LINE_START, DASHED_LINE_END],
    [0, DEBT_FILL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // During pullback, increase the debt area visibility slightly for emphasis
  const emphasisOpacity = interpolate(
    frame,
    [PULLBACK_START, PULLBACK_END],
    [0, 0.06],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const totalOpacity = fillOpacity + emphasisOpacity;

  if (frame < DASHED_LINE_START) return null;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <polygon
        points={polygonPoints}
        fill={DEBT_FILL_COLOR}
        opacity={totalOpacity}
      />
      {/* "Technical debt" label inside the shaded area */}
      {totalOpacity > 0.05 && (
        <text
          x={mapX(2016)}
          y={mapY(0.55)}
          fill={DEBT_FILL_COLOR}
          opacity={interpolate(
            frame,
            [DASHED_LINE_END, DASHED_LINE_END + 30],
            [0, 0.7],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }
          )}
          fontSize={16}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
          fontStyle="italic"
        >
          Technical debt
        </text>
      )}
    </svg>
  );
};

export default DebtArea;
