import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  STEP_WIDTH,
  STEP_HEIGHT,
  STEP_SURFACE_COLOR,
  STEP_SURFACE_OPACITY,
  STEP_STROKE_COLOR,
  STEP_STROKE_OPACITY,
  STEP_RISER_COLOR,
  STEP_RISER_STROKE_OPACITY,
  ANIM,
} from "./constants";

interface StaircaseStepProps {
  x: number;
  y: number;
  localFrame: number;
}

export const StaircaseStep: React.FC<StaircaseStepProps> = ({
  x,
  y,
  localFrame,
}) => {
  const drawProgress = interpolate(
    localFrame,
    [0, ANIM.STEP_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (drawProgress <= 0) return null;

  const surfaceOpacity = STEP_SURFACE_OPACITY * drawProgress;
  const strokeOpacity = STEP_STROKE_OPACITY * drawProgress;
  const riserStrokeOpacity = STEP_RISER_STROKE_OPACITY * drawProgress;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y - STEP_HEIGHT,
        width: STEP_WIDTH,
        height: STEP_HEIGHT,
        opacity: drawProgress,
      }}
    >
      {/* Step surface (top) */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: STEP_WIDTH,
          height: STEP_HEIGHT * 0.7,
          backgroundColor: STEP_SURFACE_COLOR,
          opacity: surfaceOpacity,
          borderTop: `2px solid ${STEP_STROKE_COLOR}`,
          borderLeft: `2px solid ${STEP_STROKE_COLOR}`,
          borderRight: `2px solid ${STEP_STROKE_COLOR}`,
          borderTopColor: `rgba(51, 65, 85, ${strokeOpacity})`,
          borderLeftColor: `rgba(51, 65, 85, ${strokeOpacity})`,
          borderRightColor: `rgba(51, 65, 85, ${strokeOpacity})`,
        }}
      />
      {/* Step riser (front face) */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: STEP_HEIGHT * 0.7,
          width: STEP_WIDTH,
          height: STEP_HEIGHT * 0.3,
          backgroundColor: STEP_RISER_COLOR,
          opacity: surfaceOpacity,
          borderBottom: `2px solid ${STEP_STROKE_COLOR}`,
          borderLeft: `2px solid ${STEP_STROKE_COLOR}`,
          borderRight: `2px solid ${STEP_STROKE_COLOR}`,
          borderBottomColor: `rgba(51, 65, 85, ${riserStrokeOpacity})`,
          borderLeftColor: `rgba(51, 65, 85, ${riserStrokeOpacity})`,
          borderRightColor: `rgba(51, 65, 85, ${riserStrokeOpacity})`,
        }}
      />
    </div>
  );
};
