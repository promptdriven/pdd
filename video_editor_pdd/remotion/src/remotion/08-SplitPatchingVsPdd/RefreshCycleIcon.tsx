import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  ICON_SIZE,
  GREEN,
  GREEN_ICON_OPACITY,
  RIGHT_HEADER_FADE_START,
  RIGHT_HEADER_FADE_END,
} from "./constants";

export const RefreshCycleIcon: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [RIGHT_HEADER_FADE_START, RIGHT_HEADER_FADE_END],
    [0, GREEN_ICON_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Gentle rotation during hold
  const rotation = interpolate(frame, [RIGHT_HEADER_FADE_END, 300], [0, 360], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        width: ICON_SIZE,
        height: ICON_SIZE,
        opacity,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      <svg
        width={ICON_SIZE}
        height={ICON_SIZE}
        viewBox="0 0 100 100"
        style={{ transform: `rotate(${rotation}deg)` }}
      >
        {/* Circular refresh arrow path */}
        <path
          d="M 50 15 A 35 35 0 1 1 20 65"
          fill="none"
          stroke={GREEN}
          strokeWidth={4}
          strokeLinecap="round"
        />
        {/* Arrow head at the end */}
        <polygon
          points="14,58 20,68 28,60"
          fill={GREEN}
        />

        {/* Second arrow on opposite side */}
        <path
          d="M 50 85 A 35 35 0 1 1 80 35"
          fill="none"
          stroke={GREEN}
          strokeWidth={4}
          strokeLinecap="round"
        />
        <polygon
          points="86,42 80,32 72,40"
          fill={GREEN}
        />

        {/* Center checkmark */}
        <path
          d="M 38 50 L 46 58 L 62 42"
          fill="none"
          stroke={GREEN}
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>
    </div>
  );
};

export default RefreshCycleIcon;
