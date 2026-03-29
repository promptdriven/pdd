import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  GENERATE_LINE_COLOR,
  PATCH_LINE_COLOR,
  SMALL_CODEBASE_COLOR,
  LARGE_CODEBASE_COLOR,
  DEBT_AREA_COLOR,
  GENERATE_LINE_DATA,
  PATCH_LINE_DATA,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  FORK_POINT,
  FORK_START,
  FORK_DIVERGE_END,
  FORK_EXTEND_END,
  CHART_APPEAR_END,
  mapX,
  mapY,
  dataToCurvePath,
} from "./constants";

/** Interpolate along a path data array, returning a partial data array up to progress [0..1]. */
function partialData(
  data: { x: number; y: number }[],
  progress: number
): { x: number; y: number }[] {
  if (progress <= 0) return [data[0]];
  if (progress >= 1) return data;

  const totalSegments = data.length - 1;
  const exactSegment = progress * totalSegments;
  const segIndex = Math.floor(exactSegment);
  const segProgress = exactSegment - segIndex;

  const result = data.slice(0, segIndex + 1);
  if (segIndex < totalSegments) {
    const from = data[segIndex];
    const to = data[segIndex + 1];
    result.push({
      x: from.x + (to.x - from.x) * segProgress,
      y: from.y + (to.y - from.y) * segProgress,
    });
  }
  return result;
}

export const ForkingLines: React.FC = () => {
  const frame = useCurrentFrame();

  // Generate line draws in during chart appear phase
  const generateProgress = interpolate(frame, [0, CHART_APPEAR_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Patch line (pre-fork amber) draws in during chart appear phase
  const patchProgress = interpolate(
    frame,
    [10, CHART_APPEAR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Fork progress: from FORK_START, lines begin to diverge
  // Phase 1 diverge (90-210): initial fork
  const forkPhase1 = interpolate(
    frame,
    [FORK_START, FORK_DIVERGE_END],
    [0, 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Phase 2 extend (210-420): fork extends fully
  const forkPhase2 = interpolate(
    frame,
    [FORK_DIVERGE_END, FORK_EXTEND_END],
    [0.5, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const forkProgress = frame < FORK_START ? 0 : frame < FORK_DIVERGE_END ? forkPhase1 : forkPhase2;

  // Fork visibility
  const forkOpacity = interpolate(frame, [FORK_START, FORK_START + 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Compute partial data for fork lines
  const smallPartial = partialData(SMALL_CODEBASE_DATA, forkProgress);
  const largePartial = partialData(LARGE_CODEBASE_DATA, forkProgress);

  // Generate line partial
  const genPartial = partialData(GENERATE_LINE_DATA, generateProgress);

  // Patch line partial
  const patchPartial = partialData(PATCH_LINE_DATA, patchProgress);

  // Debt area: area between generate line and patch line
  const debtAreaOpacity = interpolate(frame, [30, 60], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Build debt area path (between patch line top and generate line bottom)
  const debtAreaPath = React.useMemo(() => {
    if (PATCH_LINE_DATA.length < 2 || GENERATE_LINE_DATA.length < 2) return "";
    // Find overlapping x-range
    const xStart = Math.max(PATCH_LINE_DATA[0].x, GENERATE_LINE_DATA[0].x);
    const xEnd = 2020; // Up to fork point

    // Sample points
    const steps = 20;
    const topPoints: string[] = [];
    const bottomPoints: string[] = [];

    for (let i = 0; i <= steps; i++) {
      const x = xStart + (xEnd - xStart) * (i / steps);
      // Interpolate patch line (lower on chart = higher y pixel)
      const patchY = interpolateDataAtX(PATCH_LINE_DATA, x);
      // Interpolate generate line (higher on chart = lower y pixel)
      const genY = interpolateDataAtX(GENERATE_LINE_DATA, x);

      if (patchY !== null && genY !== null && genY > patchY) {
        topPoints.push(`${mapX(x)},${mapY(genY)}`);
        bottomPoints.push(`${mapX(x)},${mapY(patchY)}`);
      }
    }

    if (topPoints.length < 2) return "";
    return `M ${topPoints.join(" L ")} L ${bottomPoints.reverse().join(" L ")} Z`;
  }, []);

  // Fork label positions
  const smallLabelPos = smallPartial.length > 0
    ? smallPartial[smallPartial.length - 1]
    : FORK_POINT;
  const largeLabelPos = largePartial.length > 0
    ? largePartial[largePartial.length - 1]
    : FORK_POINT;

  const labelOpacity = interpolate(frame, [FORK_START + 30, FORK_START + 50], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Debt area fill */}
      {debtAreaPath && (
        <path
          d={debtAreaPath}
          fill={DEBT_AREA_COLOR}
          opacity={debtAreaOpacity}
        />
      )}

      {/* Generate line (blue) */}
      <path
        d={dataToCurvePath(genPartial)}
        fill="none"
        stroke={GENERATE_LINE_COLOR}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Generate line label */}
      {generateProgress > 0.8 && (
        <text
          x={mapX(GENERATE_LINE_DATA[GENERATE_LINE_DATA.length - 1].x) + 10}
          y={mapY(GENERATE_LINE_DATA[GENERATE_LINE_DATA.length - 1].y) - 8}
          fill={GENERATE_LINE_COLOR}
          fontSize={13}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={interpolate(frame, [60, 80], [0, 0.9], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Generate
        </text>
      )}

      {/* Patch line (amber, pre-fork) */}
      <path
        d={dataToCurvePath(patchPartial)}
        fill="none"
        stroke={PATCH_LINE_COLOR}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Patch line label */}
      {patchProgress > 0.7 && (
        <text
          x={mapX(2017)}
          y={mapY(0.28) - 12}
          fill={PATCH_LINE_COLOR}
          fontSize={13}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={interpolate(frame, [50, 70], [0, 0.9], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Patch
        </text>
      )}

      {/* Small codebase fork (green) */}
      {forkProgress > 0 && (
        <path
          d={dataToCurvePath(smallPartial)}
          fill="none"
          stroke={SMALL_CODEBASE_COLOR}
          strokeWidth={3}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={forkOpacity}
        />
      )}

      {/* Large codebase fork (red) */}
      {forkProgress > 0 && (
        <path
          d={dataToCurvePath(largePartial)}
          fill="none"
          stroke={LARGE_CODEBASE_COLOR}
          strokeWidth={3}
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={forkOpacity}
        />
      )}

      {/* Fork point indicator */}
      {forkProgress > 0 && (
        <circle
          cx={mapX(FORK_POINT.x)}
          cy={mapY(FORK_POINT.y)}
          r={5}
          fill={PATCH_LINE_COLOR}
          stroke="#0A0F1A"
          strokeWidth={2}
          opacity={forkOpacity}
        />
      )}

      {/* Small codebase label */}
      {forkProgress > 0.15 && (
        <text
          x={mapX(smallLabelPos.x) + 12}
          y={mapY(smallLabelPos.y) + 5}
          fill={SMALL_CODEBASE_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={labelOpacity}
        >
          Small codebase
        </text>
      )}

      {/* Large codebase label */}
      {forkProgress > 0.15 && (
        <text
          x={mapX(largeLabelPos.x) + 12}
          y={mapY(largeLabelPos.y) - 10}
          fill={LARGE_CODEBASE_COLOR}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={labelOpacity}
        >
          Large codebase
        </text>
      )}
    </svg>
  );
};

/** Helper: linearly interpolate a data series at a given x value. */
function interpolateDataAtX(
  data: { x: number; y: number }[],
  x: number
): number | null {
  for (let i = 0; i < data.length - 1; i++) {
    if (x >= data[i].x && x <= data[i + 1].x) {
      const t = (x - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + (data[i + 1].y - data[i].y) * t;
    }
  }
  return null;
}

export default ForkingLines;
