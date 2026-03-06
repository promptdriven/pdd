import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface CalloutBadgeProps {
  text: string;
  color: string;
  appearStart: number;
  appearEnd: number;
  x: number;
  y: number;
}

export const CalloutBadge: React.FC<CalloutBadgeProps> = ({
  text,
  color,
  appearStart,
  appearEnd,
  x,
  y,
}) => {
  const frame = useCurrentFrame();

  const slideX = interpolate(
    frame,
    [appearStart, appearEnd],
    [100, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame,
    [appearStart, appearEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (frame < appearStart) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        transform: `translateX(${slideX}px)`,
        opacity,
        display: "flex",
        alignItems: "center",
        padding: "10px 20px",
        backgroundColor: `${color}20`,
        border: `1.5px solid ${color}`,
        borderRadius: 24,
        whiteSpace: "nowrap",
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 600,
          fontSize: 16,
          color,
        }}
      >
        {text}
      </span>
    </div>
  );
};

export default CalloutBadge;
