import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CHART, TIMING, COLORS, interpolateY, PATCHING_POINTS, PDD_POINTS } from './constants';

export const Annotations: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.annotationsStart;
  if (localFrame < 0) return null;

  const slideProgress = interpolate(
    localFrame,
    [0, TIMING.annotationsDuration],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  const offsetX = interpolate(slideProgress, [0, 1], [30, 0]);
  const opacity = slideProgress * 0.6;

  // Annotation positions
  const annotX = 1100;
  const patchAnnotY = 280;
  const pddAnnotY = 760;

  // Leader line targets: roughly where curves are at x=1100
  const patchCurveY = interpolateY(PATCHING_POINTS, 1100);
  const pddCurveY = interpolateY(PDD_POINTS, 1100);

  return (
    <svg
      width={CHART.width}
      height={CHART.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Upper annotation: "Each patch adds debt" */}
      <g opacity={opacity} transform={`translate(${offsetX}, 0)`}>
        {/* Leader line */}
        <line
          x1={annotX}
          y1={patchAnnotY + 16}
          x2={annotX - 10}
          y2={patchCurveY}
          stroke={COLORS.patching}
          strokeWidth={1}
          opacity={0.4}
        />
        {/* Arrow glyph (upward) */}
        <text
          x={annotX - 18}
          y={patchAnnotY + 4}
          fontFamily="Inter, sans-serif"
          fontSize={14}
          fill={COLORS.patching}
        >
          {'↑'}
        </text>
        {/* Text */}
        <text
          x={annotX}
          y={patchAnnotY}
          fontFamily="Inter, sans-serif"
          fontSize={13}
          fontStyle="italic"
          fill={COLORS.patching}
        >
          Each patch adds debt
        </text>
      </g>

      {/* Lower annotation: "Each test constrains all future generations" */}
      <g opacity={opacity} transform={`translate(${offsetX}, 0)`}>
        {/* Leader line */}
        <line
          x1={annotX}
          y1={pddAnnotY - 10}
          x2={annotX - 10}
          y2={pddCurveY}
          stroke={COLORS.pdd}
          strokeWidth={1}
          opacity={0.4}
        />
        {/* Lock/check glyph */}
        <text
          x={annotX - 18}
          y={pddAnnotY + 4}
          fontFamily="Inter, sans-serif"
          fontSize={14}
          fill={COLORS.pdd}
        >
          {'✓'}
        </text>
        {/* Text */}
        <text
          x={annotX}
          y={pddAnnotY}
          fontFamily="Inter, sans-serif"
          fontSize={13}
          fontStyle="italic"
          fill={COLORS.pdd}
        >
          Each test constrains all future generations
        </text>
      </g>
    </svg>
  );
};
