import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  CONNECTOR_OPACITY,
  CONNECTOR_STROKE_WIDTH,
} from "./constants";

interface ConnectorLabelProps {
  /** Label text */
  text: string;
  /** Label color */
  color: string;
  /** Label position [x, y] */
  labelX: number;
  labelY: number;
  /** Connector start (from segment edge) */
  connectorFromX: number;
  connectorFromY: number;
  /** Frame when fade-in begins */
  fadeStartFrame: number;
  /** Duration of fade-in in frames */
  fadeDuration: number;
}

export const ConnectorLabel: React.FC<ConnectorLabelProps> = ({
  text,
  color,
  labelX,
  labelY,
  connectorFromX,
  connectorFromY,
  fadeStartFrame,
  fadeDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + fadeDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (opacity <= 0) return null;

  // Connector elbow: from segment edge → horizontal jog → label
  const elbowX = connectorFromX + (labelX - connectorFromX) * 0.5;

  return (
    <g opacity={opacity}>
      {/* Connector line */}
      <line
        x1={connectorFromX}
        y1={connectorFromY}
        x2={elbowX}
        y2={connectorFromY}
        stroke={color}
        strokeWidth={CONNECTOR_STROKE_WIDTH}
        opacity={CONNECTOR_OPACITY}
      />
      <line
        x1={elbowX}
        y1={connectorFromY}
        x2={labelX - 8}
        y2={labelY}
        stroke={color}
        strokeWidth={CONNECTOR_STROKE_WIDTH}
        opacity={CONNECTOR_OPACITY}
      />
      {/* Label text */}
      <text
        x={labelX}
        y={labelY + 6}
        fontFamily={FONT_FAMILY}
        fontSize={LABEL_FONT_SIZE}
        fontWeight={LABEL_FONT_WEIGHT}
        fill={color}
        textAnchor="start"
        dominantBaseline="middle"
      >
        {text}
      </text>
    </g>
  );
};
