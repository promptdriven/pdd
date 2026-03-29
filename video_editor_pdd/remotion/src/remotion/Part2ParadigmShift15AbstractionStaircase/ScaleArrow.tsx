import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ARROW_COLOR,
  ARROW_OPACITY,
  ARROW_DRAW_DURATION,
  type StepDef,
} from "./constants";

interface ScaleArrowProps {
  /** The step this arrow originates from (lower step) */
  fromStep: StepDef;
  /** The step this arrow points to (upper step) */
  toStep: StepDef;
  /** Frame at which arrow begins drawing */
  enterFrame: number;
}

const ScaleArrow: React.FC<ScaleArrowProps> = ({
  fromStep,
  toStep,
  enterFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - enterFrame;

  if (relFrame < 0) return null;

  const drawProgress = interpolate(
    relFrame,
    [0, ARROW_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.poly(3)),
    }
  );

  const opacity = interpolate(relFrame, [0, 10], [0, ARROW_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Arrow goes from the right edge of fromStep up to the left edge of toStep
  const startX = fromStep.x2;
  const startY = fromStep.y + fromStep.stepHeight / 2;
  const endX = toStep.x1;
  const endY = toStep.y + toStep.stepHeight / 2;

  // Curved path: go right then up with a nice curve
  const midX = (startX + endX) / 2;
  const midY = startY - 40; // curve upward

  // Build the path
  const pathD = `M ${startX} ${startY} Q ${midX} ${midY} ${endX} ${endY}`;

  // Label position (along the curve midpoint)
  const labelX = midX;
  const labelY = midY - 8;

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
        <defs>
          <marker
            id={`arrowhead-${fromStep.decade}`}
            markerWidth="8"
            markerHeight="6"
            refX="7"
            refY="3"
            orient="auto"
          >
            <polygon
              points="0 0, 8 3, 0 6"
              fill={ARROW_COLOR}
              opacity={ARROW_OPACITY}
            />
          </marker>
        </defs>

        {/* Arrow path */}
        <path
          d={pathD}
          fill="none"
          stroke={ARROW_COLOR}
          strokeWidth={2}
          opacity={opacity}
          strokeDasharray={`${drawProgress * 300} 300`}
          markerEnd={
            drawProgress > 0.8
              ? `url(#arrowhead-${fromStep.decade})`
              : undefined
          }
        />
      </svg>

      {/* "Couldn't scale" label */}
      {drawProgress > 0.3 && (
        <div
          style={{
            position: "absolute",
            left: labelX - 50,
            top: labelY - 10,
            width: 100,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 12,
            fontWeight: 400,
            color: ARROW_COLOR,
            opacity: interpolate(
              drawProgress,
              [0.3, 0.6],
              [0, ARROW_OPACITY],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }
            ),
            whiteSpace: "nowrap",
          }}
        >
          Couldn't scale
        </div>
      )}
    </div>
  );
};

export default ScaleArrow;
