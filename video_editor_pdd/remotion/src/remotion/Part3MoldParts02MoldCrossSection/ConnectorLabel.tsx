import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_OUTER_WIDTH,
  MOLD_OUTER_HEIGHT,
  MOLD_INNER_WIDTH,
  MOLD_INNER_HEIGHT,
  NOZZLE_HEIGHT,
  LABEL_FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_FADE_DURATION,
  CONNECTOR_LINE_WIDTH,
  CONNECTOR_LINE_OPACITY,
  CONNECTOR_LINE_LENGTH,
} from "./constants";

type LabelPosition = "left" | "top" | "bottom";

interface ConnectorLabelProps {
  text: string;
  color: string;
  position: LabelPosition;
  /** Absolute frame when the label starts fading in */
  startFrame: number;
}

export const ConnectorLabel: React.FC<ConnectorLabelProps> = ({
  text,
  color,
  position,
  startFrame,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (opacity <= 0) return null;

  // ── Geometry anchors ──
  const outerLeft = MOLD_CENTER_X - MOLD_OUTER_WIDTH / 2;
  const outerTop = MOLD_CENTER_Y - MOLD_OUTER_HEIGHT / 2;
  const innerTop = MOLD_CENTER_Y - MOLD_INNER_HEIGHT / 2 + 30;

  let lineX1: number;
  let lineY1: number;
  let lineX2: number;
  let lineY2: number;
  let textX: number;
  let textY: number;
  let textAnchor: string;

  if (position === "left") {
    // From mid-left wall outward
    const wallMidY = MOLD_CENTER_Y;
    lineX1 = outerLeft;
    lineY1 = wallMidY;
    lineX2 = outerLeft - CONNECTOR_LINE_LENGTH;
    lineY2 = wallMidY;
    textX = lineX2 - 12;
    textY = wallMidY;
    textAnchor = "end";
  } else if (position === "top") {
    // From nozzle top upward
    const nozzleTopY = outerTop - NOZZLE_HEIGHT;
    lineX1 = MOLD_CENTER_X;
    lineY1 = nozzleTopY;
    lineX2 = MOLD_CENTER_X;
    lineY2 = nozzleTopY - CONNECTOR_LINE_LENGTH;
    textX = MOLD_CENTER_X;
    textY = lineY2 - 12;
    textAnchor = "middle";
  } else {
    // bottom — from inner cavity bottom downward
    const cavityBottom = innerTop + MOLD_INNER_HEIGHT;
    lineX1 = MOLD_CENTER_X;
    lineY1 = cavityBottom;
    lineX2 = MOLD_CENTER_X;
    lineY2 = cavityBottom + CONNECTOR_LINE_LENGTH;
    textX = MOLD_CENTER_X;
    textY = lineY2 + 24;
    textAnchor = "middle";
  }

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Connector line */}
      <line
        x1={lineX1}
        y1={lineY1}
        x2={lineX2}
        y2={lineY2}
        stroke={color}
        strokeWidth={CONNECTOR_LINE_WIDTH}
        opacity={CONNECTOR_LINE_OPACITY * opacity}
      />
      {/* Label */}
      <text
        x={textX}
        y={textY}
        fill={color}
        fontFamily={LABEL_FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE}
        fontWeight={LABEL_FONT_WEIGHT}
        textAnchor={textAnchor}
        dominantBaseline="middle"
        opacity={opacity}
      >
        {text}
      </text>
    </svg>
  );
};

export default ConnectorLabel;
