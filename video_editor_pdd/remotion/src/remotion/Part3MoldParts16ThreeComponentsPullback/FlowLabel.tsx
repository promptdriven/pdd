// FlowLabel.tsx — animated label for each pipeline stage
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { LABEL_FADE_FRAMES } from "./constants";

interface FlowLabelProps {
  text: string;
  color: string;
  x: number;
  y: number;
  /** Frame at which this label begins fading in (relative to parent Sequence) */
  appearFrame: number;
  /** Optional connecting line to the mold */
  lineToX?: number;
}

export const FlowLabel: React.FC<FlowLabelProps> = ({
  text,
  color,
  x,
  y,
  appearFrame,
  lineToX,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - appearFrame;

  if (localFrame < 0) return null;

  const opacity = interpolate(
    localFrame,
    [0, LABEL_FADE_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const slideX = interpolate(
    localFrame,
    [0, LABEL_FADE_FRAMES],
    [x < 960 ? -20 : 20, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <g opacity={opacity} transform={`translate(${slideX}, 0)`}>
      {/* Connecting dashed line */}
      {lineToX !== undefined && (
        <line
          x1={x + (x < 960 ? text.length * 8 : -10)}
          y1={y}
          x2={lineToX}
          y2={y}
          stroke={color}
          strokeWidth={1}
          strokeDasharray="4 3"
          opacity={0.5}
        />
      )}

      {/* Background pill */}
      <rect
        x={x - 8}
        y={y - 14}
        width={text.length * 9 + 16}
        height={26}
        rx={4}
        fill={color}
        opacity={0.12}
      />

      {/* Label text */}
      <text
        x={x}
        y={y + 4}
        fill={color}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fontWeight={600}
        opacity={0.92}
      >
        {text}
      </text>
    </g>
  );
};

export default FlowLabel;
