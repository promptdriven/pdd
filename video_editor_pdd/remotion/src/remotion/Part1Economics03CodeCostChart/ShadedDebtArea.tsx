import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  IMMEDIATE_PATCH_DATA,
  TOTAL_COST_DEBT_DATA,
  DEBT_FILL_COLOR,
  DEBT_FILL_OPACITY,
  dataToPixelX,
  dataToPixelY,
  DASHED_START,
  DASHED_END,
} from "./constants";

export const ShadedDebtArea: React.FC = () => {
  const frame = useCurrentFrame();

  const fillProgress = interpolate(
    frame - DASHED_START,
    [0, DASHED_END - DASHED_START],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < DASHED_START) return null;

  // Build the filled polygon:
  // Upper boundary = total cost debt (go left to right)
  // Lower boundary = immediate patch (go right to left)
  const upperPoints = TOTAL_COST_DEBT_DATA.map(
    (pt) => `${dataToPixelX(pt.x)},${dataToPixelY(pt.y)}`
  );
  const lowerPoints = [...IMMEDIATE_PATCH_DATA]
    .reverse()
    .map((pt) => `${dataToPixelX(pt.x)},${dataToPixelY(pt.y)}`);

  const polygonPoints = [...upperPoints, ...lowerPoints].join(" ");

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: "none",
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", left: 0, top: 0 }}
      >
        <polygon
          points={polygonPoints}
          fill={DEBT_FILL_COLOR}
          opacity={DEBT_FILL_OPACITY * fillProgress}
        />
      </svg>
    </div>
  );
};

export default ShadedDebtArea;
