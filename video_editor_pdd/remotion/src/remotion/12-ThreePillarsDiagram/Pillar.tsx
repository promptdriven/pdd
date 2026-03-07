import React from "react";
import { useCurrentFrame, useVideoConfig, spring, interpolate } from "remotion";
import { PillarIcon } from "./PillarIcon";
import { PILLAR_WIDTH, PILLAR_HEIGHT, PILLAR_RADIUS } from "./constants";

interface PillarProps {
  label: string;
  icon: "document" | "checkmark" | "loop";
  color: string;
  x: number;
  y: number;
  inStart: number;
  inEnd: number;
}

export const Pillar: React.FC<PillarProps> = ({
  label,
  icon,
  color,
  x,
  y,
  inStart,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const springProgress = spring({
    frame: frame - inStart,
    fps,
    config: { damping: 14, stiffness: 200 },
  });

  const opacity = Math.min(1, springProgress);
  const translateY = interpolate(springProgress, [0, 1], [40, 0]);

  if (frame < inStart) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y - PILLAR_HEIGHT / 2,
        width: PILLAR_WIDTH,
        height: PILLAR_HEIGHT,
        opacity,
        transform: `translateY(${translateY}px)`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 8,
        borderRadius: PILLAR_RADIUS,
        border: `2px solid ${color}`,
        backgroundColor: `${color}20`,
      }}
    >
      <PillarIcon icon={icon} color={color} size={28} />
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 700,
          fontSize: 24,
          color: "#FFFFFF",
          lineHeight: 1,
        }}
      >
        {label}
      </span>
    </div>
  );
};
