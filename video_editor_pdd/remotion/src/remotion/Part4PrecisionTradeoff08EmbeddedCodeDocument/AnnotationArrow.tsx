import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ANNOTATION_SIZE,
  ANNOTATION_OPACITY,
  ANNOTATION_START,
  ANNOTATION_DRAW_DURATION,
} from "./constants";

interface AnnotationArrowProps {
  /** Arrow tip x (points toward document) */
  tipX: number;
  /** Arrow tip y */
  tipY: number;
  /** Label text */
  label: string;
  /** Arrow / label color */
  color: string;
  /** Stagger offset in frames from ANNOTATION_START */
  delay?: number;
}

const ARROW_LENGTH = 60;
const ARROW_HEAD_SIZE = 8;
const LABEL_GAP = 10;

const AnnotationArrow: React.FC<AnnotationArrowProps> = ({
  tipX,
  tipY,
  label,
  color,
  delay = 0,
}) => {
  const frame = useCurrentFrame();

  const drawStart = ANNOTATION_START + delay;
  const drawEnd = drawStart + ANNOTATION_DRAW_DURATION;

  const progress = interpolate(frame, [drawStart, drawEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  if (progress <= 0) return null;

  const tailX = tipX - ARROW_LENGTH;
  const currentTipX = tailX + ARROW_LENGTH * progress;

  // Arrow line coordinates (SVG)
  const svgWidth = ARROW_LENGTH + 20;
  const svgHeight = 40;

  return (
    <div
      style={{
        position: "absolute",
        left: tipX - ARROW_LENGTH - 120,
        top: tipY - svgHeight / 2,
        display: "flex",
        alignItems: "center",
        opacity: progress,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: ANNOTATION_SIZE,
          fontWeight: 400,
          color,
          opacity: ANNOTATION_OPACITY,
          marginRight: LABEL_GAP,
          whiteSpace: "nowrap",
        }}
      >
        {label}
      </div>

      {/* Arrow SVG */}
      <svg
        width={svgWidth}
        height={svgHeight}
        viewBox={`0 0 ${svgWidth} ${svgHeight}`}
        style={{ overflow: "visible" }}
      >
        {/* Line */}
        <line
          x1={0}
          y1={svgHeight / 2}
          x2={ARROW_LENGTH * progress}
          y2={svgHeight / 2}
          stroke={color}
          strokeWidth={1.5}
          strokeOpacity={ANNOTATION_OPACITY}
        />
        {/* Arrowhead */}
        {progress > 0.5 && (
          <polygon
            points={`
              ${ARROW_LENGTH * progress},${svgHeight / 2}
              ${ARROW_LENGTH * progress - ARROW_HEAD_SIZE},${svgHeight / 2 - ARROW_HEAD_SIZE / 2}
              ${ARROW_LENGTH * progress - ARROW_HEAD_SIZE},${svgHeight / 2 + ARROW_HEAD_SIZE / 2}
            `}
            fill={color}
            opacity={ANNOTATION_OPACITY}
          />
        )}
      </svg>
    </div>
  );
};

export default AnnotationArrow;
