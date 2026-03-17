import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  COMPILER_COLOR,
  COMPILER_OPACITY,
  COMPILER_LABEL_OPACITY,
  COMPILER_LABEL_SIZE,
  UI_FONT,
} from "./constants";

interface CompilerIconProps {
  x: number;
  y: number;
  size: number;
  appearStart: number;
  appearEnd: number;
  pulse?: boolean;
}

export const CompilerIcon: React.FC<CompilerIconProps> = ({
  x,
  y,
  size,
  appearStart,
  appearEnd,
  pulse = false,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [appearStart, appearEnd],
    [0, COMPILER_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < appearStart) return null;

  // Pulse effect
  const pulseScale = pulse
    ? 1 + 0.05 * Math.sin(((frame - appearStart) / 15) * Math.PI * 2)
    : 1;

  const half = size / 2;

  return (
    <>
      {/* Gear/processor icon */}
      <svg
        width={size}
        height={size}
        viewBox="0 0 60 60"
        style={{
          position: "absolute",
          left: x - half,
          top: y - half,
          opacity,
          transform: `scale(${pulseScale})`,
          transformOrigin: "center",
          pointerEvents: "none",
        }}
      >
        {/* Gear teeth */}
        <path
          d={`
            M 26 4 L 34 4 L 36 10 L 38 11 L 44 7 L 50 13 L 46 19 L 47 21 L 53 23
            L 53 31 L 47 33 L 46 35 L 50 41 L 44 47 L 38 43 L 36 44 L 34 50
            L 26 50 L 24 44 L 22 43 L 16 47 L 10 41 L 14 35 L 13 33 L 7 31
            L 7 23 L 13 21 L 14 19 L 10 13 L 16 7 L 22 11 L 24 10 Z
          `}
          fill="none"
          stroke={COMPILER_COLOR}
          strokeWidth={1.5}
          strokeLinejoin="round"
        />
        {/* Center circle */}
        <circle cx={30} cy={27} r={8} fill="none" stroke={COMPILER_COLOR} strokeWidth={1.5} />
      </svg>

      {/* Label */}
      <div
        style={{
          position: "absolute",
          left: x - 40,
          top: y + half + 4,
          width: 80,
          textAlign: "center",
          fontFamily: UI_FONT,
          fontSize: COMPILER_LABEL_SIZE,
          color: COMPILER_COLOR,
          opacity: opacity * (COMPILER_LABEL_OPACITY / COMPILER_OPACITY),
          pointerEvents: "none",
        }}
      >
        Synthesis
      </div>
    </>
  );
};

export default CompilerIcon;
