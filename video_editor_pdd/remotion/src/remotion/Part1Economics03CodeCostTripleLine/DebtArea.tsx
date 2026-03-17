import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  AMBER_LINE_COLOR,
  DEBT_FILL_START,
  DEBT_FILL_END,
  DEBT_PULSE_CYCLE,
  DEBT_OPACITY_MIN,
  DEBT_OPACITY_MAX,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

/**
 * Build an SVG polygon path that fills the area between
 * the dashed (total cost) line above and the solid (patch cost) line below.
 */
function buildAreaPath(): string {
  // Walk the upper line (total cost) left-to-right
  const upperPts = TOTAL_COST_DATA.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));
  // Walk the lower line (patch cost) right-to-left
  const lowerPts = PATCH_COST_DATA.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  })).reverse();

  const all = [...upperPts, ...lowerPts];
  if (all.length === 0) return "";

  let d = `M ${all[0].x} ${all[0].y}`;
  for (let i = 1; i < all.length; i++) {
    d += ` L ${all[i].x} ${all[i].y}`;
  }
  d += " Z";
  return d;
}

export const DebtArea: React.FC = () => {
  const frame = useCurrentFrame();

  const areaPath = useMemo(() => buildAreaPath(), []);

  // Fill-in progress (clipRect reveal from left to right)
  const fillProgress = interpolate(
    frame,
    [DEBT_FILL_START, DEBT_FILL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse opacity after fully filled
  const pulsePhase = (frame - DEBT_FILL_END) / DEBT_PULSE_CYCLE;
  const isPulsing = frame >= DEBT_FILL_END;
  const pulseOpacity = isPulsing
    ? DEBT_OPACITY_MIN +
      (DEBT_OPACITY_MAX - DEBT_OPACITY_MIN) *
        (0.5 + 0.5 * Math.sin(pulsePhase * Math.PI * 2))
    : DEBT_OPACITY_MIN;

  const baseOpacity = interpolate(
    frame,
    [DEBT_FILL_START, DEBT_FILL_END],
    [0, DEBT_OPACITY_MIN],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const finalOpacity = isPulsing ? pulseOpacity : baseOpacity;

  // Clip rectangle width for left-to-right reveal
  const clipWidth = dataToPixelX(2025) * fillProgress;

  if (frame < DEBT_FILL_START) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <clipPath id="debt-clip">
            <rect x={0} y={0} width={clipWidth} height={HEIGHT} />
          </clipPath>
        </defs>
        <path
          d={areaPath}
          fill={AMBER_LINE_COLOR}
          opacity={finalOpacity}
          clipPath="url(#debt-clip)"
        />
      </svg>
    </AbsoluteFill>
  );
};

export default DebtArea;
