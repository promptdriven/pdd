import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface BoundaryCircleProps {
  cx: number;
  cy: number;
  radius: number;
  color: string;
  circleOpacity: number;
  strokeWidth: number;
  /** Frame this starts animating (relative to component mount) */
  animStart: number;
  animDuration?: number;
  /** Label shown above the circle */
  labelText: string;
  labelColor: string;
  labelOpacity: number;
  labelSize: number;
  /** Frame offset for label fade-in (relative to animStart) */
  labelDelay?: number;
}

export const BoundaryCircle: React.FC<BoundaryCircleProps> = ({
  cx,
  cy,
  radius,
  color,
  circleOpacity,
  strokeWidth,
  animStart,
  animDuration = 30,
  labelText,
  labelColor,
  labelOpacity,
  labelSize,
  labelDelay = 15,
}) => {
  const frame = useCurrentFrame();

  const circumference = 2 * Math.PI * radius;

  // Stroke-draw animation via dashoffset
  const drawProgress = interpolate(
    frame,
    [animStart, animStart + animDuration],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const dashOffset = circumference * drawProgress;

  // Label fade-in
  const labelFade = interpolate(
    frame,
    [animStart + labelDelay, animStart + labelDelay + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Only render once animation has begun
  if (frame < animStart) return null;

  return (
    <g>
      <circle
        cx={cx}
        cy={cy}
        r={radius}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeDasharray={`8 6`}
        strokeDashoffset={dashOffset}
        opacity={circleOpacity}
      />
      <text
        x={cx}
        y={cy - radius - 12}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={labelSize}
        fontWeight={400}
        fill={labelColor}
        opacity={labelFade * labelOpacity}
      >
        {labelText}
      </text>
    </g>
  );
};
