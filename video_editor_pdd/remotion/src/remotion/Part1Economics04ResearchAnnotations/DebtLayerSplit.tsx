import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_BOTTOM,
  CHART_HEIGHT,
  YEARS,
  IMMEDIATE_COST_DATA,
  TOTAL_COST_DATA,
  AMBER,
  MUTED,
  DEBT_SPLIT_START,
  DEBT_SPLIT_DURATION,
} from './constants';

/**
 * Debt Layer Decomposition: at frame DEBT_SPLIT_START, the single shaded
 * debt area separates into two visible layers:
 * - Upper: "Code Complexity" (darker)
 * - Lower: "Context Rot" (lighter, with noise texture)
 */

const indexToX = (i: number): number => {
  const chartWidth = CHART_RIGHT - CHART_LEFT;
  return CHART_LEFT + (i / (YEARS.length - 1)) * chartWidth;
};

const valueToY = (v: number): number => {
  return CHART_BOTTOM - v * CHART_HEIGHT;
};

// Build SVG path for a band between two data series
const buildBandPath = (upper: number[], lower: number[]): string => {
  const forwardPoints = upper.map((v, i) => `${indexToX(i)} ${valueToY(v)}`);
  const backwardPoints = [...lower]
    .map((v, i) => `${indexToX(i)} ${valueToY(v)}`)
    .reverse();
  return `M ${forwardPoints.join(' L ')} L ${backwardPoints.join(' L ')} Z`;
};

const DebtLayerSplit: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - DEBT_SPLIT_START;

  // Split progress: 0 = unsplit, 1 = fully split
  const splitProgress =
    localFrame < 0
      ? 0
      : interpolate(localFrame, [0, DEBT_SPLIT_DURATION], [0, 1], {
          easing: Easing.inOut(Easing.cubic),
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

  // Midpoint series: halfway between total and immediate cost
  const midData = useMemo(
    () =>
      TOTAL_COST_DATA.map(
        (v, i) => (v + IMMEDIATE_COST_DATA[i]) / 2,
      ),
    [],
  );

  // When splitProgress > 0, we show two separate layers with a gap
  // The gap is achieved by slightly offsetting the mid boundary
  const gapSize = splitProgress * 0.015; // small visual gap

  const upperLower = midData.map((v) => v + gapSize / 2);
  const lowerUpper = midData.map((v) => v - gapSize / 2);

  const upperPath = buildBandPath(TOTAL_COST_DATA, upperLower);
  const lowerPath = buildBandPath(lowerUpper, IMMEDIATE_COST_DATA);

  // Label positions (placed at roughly 2023 index = 4)
  const labelIndex = 4;
  const upperLabelY =
    valueToY((TOTAL_COST_DATA[labelIndex] + midData[labelIndex]) / 2) + 4;
  const lowerLabelY =
    valueToY((midData[labelIndex] + IMMEDIATE_COST_DATA[labelIndex]) / 2) + 4;
  const labelX = indexToX(labelIndex) - 60;

  // Noise animation for Context Rot layer
  const noiseOpacity =
    localFrame > 0
      ? 0.02 +
        0.02 *
          Math.sin(frame * 0.15) *
          Math.cos(frame * 0.07)
      : 0;

  // Dashed dividing line at the midpoint
  const dividerPath = midData
    .map((v, i) => `${i === 0 ? 'M' : 'L'} ${indexToX(i)} ${valueToY(v)}`)
    .join(' ');

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      <svg
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: '100%',
          height: '100%',
        }}
      >
        {splitProgress > 0 && (
          <>
            {/* Upper layer: Code Complexity */}
            <path d={upperPath} fill={AMBER} opacity={0.10} />

            {/* Lower layer: Context Rot */}
            <path d={lowerPath} fill={AMBER} opacity={0.05} />

            {/* Noise texture overlay on lower layer */}
            <path
              d={lowerPath}
              fill="url(#noisePattern)"
              opacity={noiseOpacity}
            />

            {/* Dividing dashed line */}
            <path
              d={dividerPath}
              fill="none"
              stroke={MUTED}
              strokeWidth={1}
              strokeDasharray="4 3"
              opacity={0.1 * splitProgress}
            />

            {/* Noise pattern definition */}
            <defs>
              <pattern
                id="noisePattern"
                x={frame % 4}
                y={frame % 3}
                width="4"
                height="4"
                patternUnits="userSpaceOnUse"
              >
                <rect
                  x={Math.sin(frame * 0.3) > 0 ? 0 : 2}
                  y={Math.cos(frame * 0.5) > 0 ? 0 : 2}
                  width="1"
                  height="1"
                  fill={AMBER}
                  opacity="0.6"
                />
                <rect
                  x={Math.sin(frame * 0.7 + 1) > 0 ? 1 : 3}
                  y={Math.cos(frame * 0.4 + 2) > 0 ? 1 : 3}
                  width="1"
                  height="1"
                  fill={AMBER}
                  opacity="0.4"
                />
              </pattern>
            </defs>
          </>
        )}
      </svg>

      {/* Layer labels */}
      {splitProgress > 0.5 && (
        <>
          <div
            style={{
              position: 'absolute',
              left: labelX,
              top: upperLabelY - 6,
              fontFamily: 'Inter, sans-serif',
              fontSize: 10,
              color: MUTED,
              opacity: 0.35 * Math.min(1, (splitProgress - 0.5) * 2),
              whiteSpace: 'nowrap',
            }}
          >
            Code Complexity
          </div>
          <div
            style={{
              position: 'absolute',
              left: labelX,
              top: lowerLabelY - 6,
              fontFamily: 'Inter, sans-serif',
              fontSize: 10,
              color: MUTED,
              opacity: 0.35 * Math.min(1, (splitProgress - 0.5) * 2),
              whiteSpace: 'nowrap',
            }}
          >
            Context Rot
          </div>
        </>
      )}
    </div>
  );
};

export default DebtLayerSplit;
