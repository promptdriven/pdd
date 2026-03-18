import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  PATCHING_COLOR,
  PDD_COLOR,
  ANNOTATIONS_START,
  ANNOTATIONS_DURATION,
} from './constants';

// Leader line target points on the curves (approximately Year 6)
const PATCHING_LEADER_TARGET: [number, number] = [1092, 370];
const PDD_LEADER_TARGET: [number, number] = [1092, 740];

// Annotation positions
const UPPER_POS: [number, number] = [1100, 280];
const LOWER_POS: [number, number] = [1100, 760];

export const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  const slideProgress = interpolate(
    frame,
    [ANNOTATIONS_START, ANNOTATIONS_START + ANNOTATIONS_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  const opacity = slideProgress * 0.6;
  const slideOffset = (1 - slideProgress) * 20;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Upper annotation: "Each patch adds debt" */}
      <g opacity={opacity} transform={`translate(${slideOffset}, 0)`}>
        {/* Leader line */}
        <line
          x1={UPPER_POS[0]}
          y1={UPPER_POS[1] + 10}
          x2={PATCHING_LEADER_TARGET[0]}
          y2={PATCHING_LEADER_TARGET[1] - 5}
          stroke={PATCHING_COLOR}
          strokeWidth={1}
          opacity={0.5}
          strokeDasharray="4 3"
        />
        {/* Arrow glyph (upward) */}
        <text
          x={UPPER_POS[0] - 18}
          y={UPPER_POS[1] + 2}
          fill={PATCHING_COLOR}
          fontFamily="Inter, sans-serif"
          fontSize={14}
        >
          ↑
        </text>
        {/* Annotation text */}
        <text
          x={UPPER_POS[0]}
          y={UPPER_POS[1]}
          fill={PATCHING_COLOR}
          fontFamily="Inter, sans-serif"
          fontSize={13}
          fontWeight={400}
          fontStyle="italic"
        >
          Each patch adds debt
        </text>
      </g>

      {/* Lower annotation: "Each test constrains all future generations" */}
      <g opacity={opacity} transform={`translate(${slideOffset}, 0)`}>
        {/* Leader line */}
        <line
          x1={LOWER_POS[0]}
          y1={LOWER_POS[1] - 10}
          x2={PDD_LEADER_TARGET[0]}
          y2={PDD_LEADER_TARGET[1] + 5}
          stroke={PDD_COLOR}
          strokeWidth={1}
          opacity={0.5}
          strokeDasharray="4 3"
        />
        {/* Lock/check glyph */}
        <text
          x={LOWER_POS[0] - 18}
          y={LOWER_POS[1] + 2}
          fill={PDD_COLOR}
          fontFamily="Inter, sans-serif"
          fontSize={14}
        >
          ✓
        </text>
        {/* Annotation text */}
        <text
          x={LOWER_POS[0]}
          y={LOWER_POS[1]}
          fill={PDD_COLOR}
          fontFamily="Inter, sans-serif"
          fontSize={13}
          fontWeight={400}
          fontStyle="italic"
        >
          Each test constrains all future generations
        </text>
      </g>
    </svg>
  );
};
