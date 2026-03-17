import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BR_CENTER_X,
  BR_CENTER_Y,
  ENTERPRISE_CIRCLE_RADIUS,
  RED,
  FONT_FAMILY,
  CIRCLE_DRAW_START,
  CIRCLE_DRAW_END,
  CIRCLE_LABEL_START,
  CIRCLE_LABEL_END,
} from "./constants";

export const EnterpriseCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Circle circumference for stroke-dashoffset draw animation
  const circumference = 2 * Math.PI * ENTERPRISE_CIRCLE_RADIUS;

  const drawProgress = interpolate(
    frame,
    [CIRCLE_DRAW_START, CIRCLE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelOpacity = interpolate(
    frame,
    [CIRCLE_LABEL_START, CIRCLE_LABEL_END],
    [0, 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // We simulate a dashed circle drawing in by controlling overall opacity
  // and the stroke-dashoffset of a solid "reveal" circle behind the dashed one
  const circleOpacity = interpolate(
    frame,
    [CIRCLE_DRAW_START, CIRCLE_DRAW_START + 5],
    [0, 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Use a clip-path approach: draw a solid circle that reveals the dashed one
  const dashOffset = circumference * (1 - drawProgress);

  return (
    <>
      {/* Invisible solid circle used as a clip/reveal mask */}
      <defs>
        <clipPath id="circleReveal">
          <circle
            cx={BR_CENTER_X}
            cy={BR_CENTER_Y}
            r={ENTERPRISE_CIRCLE_RADIUS + 4}
            strokeDasharray={`${circumference + 10} ${circumference + 10}`}
            strokeDashoffset={dashOffset}
            stroke="white"
            strokeWidth={10}
            fill="none"
          />
        </clipPath>
      </defs>

      {/* Dashed circle */}
      <circle
        cx={BR_CENTER_X}
        cy={BR_CENTER_Y}
        r={ENTERPRISE_CIRCLE_RADIUS}
        fill="none"
        stroke={RED}
        strokeWidth={2}
        strokeDasharray="8 6"
        opacity={circleOpacity}
        style={{
          // Rotate to start drawing from top
          transformOrigin: `${BR_CENTER_X}px ${BR_CENTER_Y}px`,
          transform: `rotate(-90deg)`,
        }}
      />

      {/* Subtle glow behind circle */}
      <circle
        cx={BR_CENTER_X}
        cy={BR_CENTER_Y}
        r={ENTERPRISE_CIRCLE_RADIUS - 5}
        fill={RED}
        opacity={circleOpacity * 0.05}
      />

      {/* Label below circle */}
      <text
        x={BR_CENTER_X}
        y={BR_CENTER_Y + ENTERPRISE_CIRCLE_RADIUS + 22}
        fill={RED}
        fontSize={10}
        fontFamily={FONT_FAMILY}
        fontWeight={500}
        opacity={labelOpacity}
        textAnchor="middle"
        dominantBaseline="middle"
      >
        Most enterprise work
      </text>
    </>
  );
};
