// StaircaseStep.tsx — Draws one step platform (surface + riser) with animated draw-in
import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  STEP_WIDTH,
  STEP_HEIGHT,
  COLORS,
  OPACITIES,
} from './constants';

interface StaircaseStepProps {
  x: number;
  y: number;
  startFrame: number;
  drawDuration?: number;
}

const StaircaseStep: React.FC<StaircaseStepProps> = ({
  x,
  y,
  startFrame,
  drawDuration = 20,
}) => {
  const frame = useCurrentFrame();
  const progress = interpolate(
    frame,
    [startFrame, startFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Step surface: the flat top of the step
  // Step riser: the vertical face of the step
  const surfaceOpacity = progress * OPACITIES.stepSurface;
  const strokeOpacity = progress * OPACITIES.stepStroke;
  const riserStrokeOpacity = progress * OPACITIES.riserStroke;

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      {/* Step riser (vertical face) */}
      <rect
        x={x}
        y={y}
        width={STEP_WIDTH * progress}
        height={STEP_HEIGHT}
        fill={COLORS.stepRiser}
        stroke={COLORS.stepStroke}
        strokeWidth={2}
        opacity={riserStrokeOpacity > 0 ? 1 : 0}
        fillOpacity={surfaceOpacity}
        strokeOpacity={riserStrokeOpacity}
      />
      {/* Step surface (top face — drawn as a parallelogram-ish highlight) */}
      <rect
        x={x}
        y={y}
        width={STEP_WIDTH * progress}
        height={4}
        fill={COLORS.stepSurface}
        opacity={strokeOpacity}
      />
    </svg>
  );
};

export default StaircaseStep;
