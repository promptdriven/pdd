import React from "react";
import { AbsoluteFill } from "remotion";

interface BlueprintGridProps {
  spacing: number;
  color: string;
  opacity: number;
}

export const BlueprintGrid: React.FC<BlueprintGridProps> = ({
  spacing,
  color,
  opacity,
}) => {
  const cols = Math.ceil(1920 / spacing);
  const rows = Math.ceil(1080 / spacing);

  return (
    <AbsoluteFill>
      <svg width={1920} height={1080} style={{ position: "absolute" }}>
        {Array.from({ length: cols + 1 }, (_, i) => (
          <line
            key={`v-${i}`}
            x1={i * spacing}
            y1={0}
            x2={i * spacing}
            y2={1080}
            stroke={color}
            strokeWidth={1}
            opacity={opacity}
          />
        ))}
        {Array.from({ length: rows + 1 }, (_, i) => (
          <line
            key={`h-${i}`}
            x1={0}
            y1={i * spacing}
            x2={1920}
            y2={i * spacing}
            stroke={color}
            strokeWidth={1}
            opacity={opacity}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
