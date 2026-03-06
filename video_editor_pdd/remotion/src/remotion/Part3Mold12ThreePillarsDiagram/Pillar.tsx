import React from "react";
import { PillarIcon } from "./PillarIcon";
import {
  PILLAR_WIDTH,
  PILLAR_HEIGHT,
  PILLAR_BORDER_RADIUS,
  PILLAR_BG_OPACITY,
  PILLAR_LABEL_SIZE,
  PILLAR_ICON_SIZE,
} from "./constants";

interface PillarProps {
  label: string;
  icon: "document" | "checkmark" | "loop";
  color: string;
  opacity: number;
  translateY: number;
}

export const Pillar: React.FC<PillarProps> = ({
  label,
  icon,
  color,
  opacity,
  translateY,
}) => {
  // Convert hex color to rgba for background fill
  const hexToRgba = (hex: string, alpha: number): string => {
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    return `rgba(${r}, ${g}, ${b}, ${alpha})`;
  };

  return (
    <div
      style={{
        width: PILLAR_WIDTH,
        height: PILLAR_HEIGHT,
        borderRadius: PILLAR_BORDER_RADIUS,
        backgroundColor: hexToRgba(color, PILLAR_BG_OPACITY),
        border: `2px solid ${color}`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 8,
        opacity,
        transform: `translateY(${translateY}px)`,
        flexShrink: 0,
      }}
    >
      <PillarIcon icon={icon} color={color} size={PILLAR_ICON_SIZE} />
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 700,
          fontSize: PILLAR_LABEL_SIZE,
          color: "#FFFFFF",
          lineHeight: 1,
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default Pillar;
