/**
 * DebtLayerSplit — Splits the debt shaded area into two visible layers:
 *   Upper: "Code Complexity" (darker amber)
 *   Lower: "Context Rot" (lighter amber with animated noise texture)
 *
 * Replaces the single-color debt area once the split animation begins.
 */
import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  AMBER_LINE_COLOR,
  AXIS_LABEL_COLOR,
  FONT_FAMILY,
  DEBT_SPLIT_START,
  DEBT_SPLIT_DUR,
  DEBT_OPACITY_MIN,
  DEBT_OPACITY_MAX,
  DEBT_PULSE_CYCLE,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

/** Build path for the upper debt layer (total cost → midpoint). */
function buildUpperLayerPath(splitRatio: number): string {
  const upper = TOTAL_COST_DATA.map((d, i) => {
    const patchY = PATCH_COST_DATA[i]?.y ?? d.y;
    const midY = d.y - (d.y - patchY) * splitRatio;
    return {
      topX: dataToPixelX(d.x),
      topY: dataToPixelY(d.y),
      bottomX: dataToPixelX(d.x),
      bottomY: dataToPixelY(midY),
    };
  });

  let path = `M ${upper[0].topX} ${upper[0].topY}`;
  for (let i = 1; i < upper.length; i++) {
    path += ` L ${upper[i].topX} ${upper[i].topY}`;
  }
  for (let i = upper.length - 1; i >= 0; i--) {
    path += ` L ${upper[i].bottomX} ${upper[i].bottomY}`;
  }
  path += " Z";
  return path;
}

/** Build path for the lower debt layer (midpoint → patch cost). */
function buildLowerLayerPath(splitRatio: number): string {
  const lower = TOTAL_COST_DATA.map((d, i) => {
    const patchY = PATCH_COST_DATA[i]?.y ?? d.y;
    const midY = d.y - (d.y - patchY) * splitRatio;
    return {
      topX: dataToPixelX(d.x),
      topY: dataToPixelY(midY),
      bottomX: dataToPixelX(PATCH_COST_DATA[i]?.x ?? d.x),
      bottomY: dataToPixelY(patchY),
    };
  });

  let path = `M ${lower[0].topX} ${lower[0].topY}`;
  for (let i = 1; i < lower.length; i++) {
    path += ` L ${lower[i].topX} ${lower[i].topY}`;
  }
  for (let i = lower.length - 1; i >= 0; i--) {
    path += ` L ${lower[i].bottomX} ${lower[i].bottomY}`;
  }
  path += " Z";
  return path;
}

/** Build the dividing line path between the two layers. */
function buildDividingLinePath(splitRatio: number): string {
  const pts = TOTAL_COST_DATA.map((d, i) => {
    const patchY = PATCH_COST_DATA[i]?.y ?? d.y;
    const midY = d.y - (d.y - patchY) * splitRatio;
    return { x: dataToPixelX(d.x), y: dataToPixelY(midY) };
  });

  let path = `M ${pts[0].x} ${pts[0].y}`;
  for (let i = 1; i < pts.length; i++) {
    path += ` L ${pts[i].x} ${pts[i].y}`;
  }
  return path;
}

/** Generate a pseudo-random noise pattern for the Context Rot texture. */
function generateNoiseRects(
  seed: number,
  count: number,
  boundsX: number,
  boundsY: number,
  boundsW: number,
  boundsH: number
): Array<{ x: number; y: number; w: number; h: number }> {
  const rects: Array<{ x: number; y: number; w: number; h: number }> = [];
  let s = seed;
  for (let i = 0; i < count; i++) {
    // Simple LCG pseudo-random
    s = (s * 1664525 + 1013904223) & 0xffffffff;
    const rx = boundsX + (((s >>> 16) & 0xffff) / 0xffff) * boundsW;
    s = (s * 1664525 + 1013904223) & 0xffffffff;
    const ry = boundsY + (((s >>> 16) & 0xffff) / 0xffff) * boundsH;
    rects.push({ x: rx, y: ry, w: 3, h: 2 });
  }
  return rects;
}

export const DebtLayerSplit: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < DEBT_SPLIT_START) return null;

  const localFrame = frame - DEBT_SPLIT_START;

  // Split animation: from unified (0) to separated (0.5 = middle split point)
  const splitProgress = interpolate(
    localFrame,
    [0, DEBT_SPLIT_DUR],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // The split ratio determines where the dividing line sits.
  // 0.5 = exactly halfway between total cost and patch cost.
  const splitRatio = 0.5 * splitProgress;

  const upperPath = useMemo(
    () => buildUpperLayerPath(splitRatio),
    [splitRatio]
  );
  const lowerPath = useMemo(
    () => buildLowerLayerPath(splitRatio),
    [splitRatio]
  );
  const dividingPath = useMemo(
    () => buildDividingLinePath(splitRatio),
    [splitRatio]
  );

  // Label fade-in after split completes
  const labelOpacity = interpolate(
    localFrame,
    [DEBT_SPLIT_DUR, DEBT_SPLIT_DUR + 20],
    [0, 0.35],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Noise animation for Context Rot: oscillating opacity
  const noiseOpacity =
    0.02 + 0.02 * (0.5 + 0.5 * Math.sin(frame * 0.15));

  // Noise pattern uses frame for subtle animation
  const noiseSeed = Math.floor(frame / 3); // Changes every 3 frames for subtle static effect

  // Bounds for noise rects (approximate debt area)
  const noiseBoundsX = dataToPixelX(2015);
  const noiseBoundsW = dataToPixelX(2025) - noiseBoundsX;
  const noiseBoundsY = dataToPixelY(14);
  const noiseBoundsH = dataToPixelY(2) - noiseBoundsY;

  const noiseRects = useMemo(
    () =>
      generateNoiseRects(
        noiseSeed,
        80,
        noiseBoundsX,
        noiseBoundsY,
        noiseBoundsW,
        noiseBoundsH
      ),
    [noiseSeed, noiseBoundsX, noiseBoundsY, noiseBoundsW, noiseBoundsH]
  );

  // Label positions (inside each layer, left-aligned around 2016)
  const upperLabelX = dataToPixelX(2016.5);
  const lowerLabelX = dataToPixelX(2016.5);

  // Upper label: between total cost and midpoint at ~2016
  const totalAt2016 = 14; // approx from data
  const patchAt2016 = 7.8; // approx from data
  const midAt2016 = totalAt2016 - (totalAt2016 - patchAt2016) * splitRatio;
  const upperLabelY = dataToPixelY((totalAt2016 + midAt2016) / 2) + 4;

  // Lower label: between midpoint and patch cost at ~2016
  const lowerLabelY = dataToPixelY((midAt2016 + patchAt2016) / 2) + 4;

  // Dividing line opacity
  const dividerOpacity = interpolate(
    localFrame,
    [DEBT_SPLIT_DUR * 0.5, DEBT_SPLIT_DUR],
    [0, 0.1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Pulsing base opacity
  const pulsePhase = frame / DEBT_PULSE_CYCLE;
  const basePulse =
    DEBT_OPACITY_MIN +
    (DEBT_OPACITY_MAX - DEBT_OPACITY_MIN) *
      (0.5 + 0.5 * Math.sin(pulsePhase * Math.PI * 2));

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <clipPath id="lower-layer-clip">
            <path d={lowerPath} />
          </clipPath>
        </defs>

        {/* Upper layer: Code Complexity — darker amber */}
        <path d={upperPath} fill={AMBER_LINE_COLOR} opacity={0.10} />

        {/* Lower layer: Context Rot — lighter amber */}
        <path d={lowerPath} fill={AMBER_LINE_COLOR} opacity={0.05} />

        {/* Noise texture in lower layer (clipped) */}
        <g clipPath="url(#lower-layer-clip)" opacity={noiseOpacity}>
          {noiseRects.map((r, i) => (
            <rect
              key={i}
              x={r.x}
              y={r.y}
              width={r.w}
              height={r.h}
              fill={AXIS_LABEL_COLOR}
            />
          ))}
        </g>

        {/* Dividing line between layers */}
        {splitProgress > 0.3 && (
          <path
            d={dividingPath}
            fill="none"
            stroke={AXIS_LABEL_COLOR}
            strokeWidth={1}
            strokeDasharray="4 3"
            opacity={dividerOpacity}
          />
        )}

        {/* Layer labels */}
        <text
          x={upperLabelX}
          y={upperLabelY}
          fill={AXIS_LABEL_COLOR}
          fontSize={10}
          fontFamily="Inter, sans-serif"
          fontWeight={400}
          opacity={labelOpacity}
        >
          Code Complexity
        </text>
        <text
          x={lowerLabelX}
          y={lowerLabelY}
          fill={AXIS_LABEL_COLOR}
          fontSize={10}
          fontFamily="Inter, sans-serif"
          fontWeight={400}
          opacity={labelOpacity}
        >
          Context Rot
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default DebtLayerSplit;
