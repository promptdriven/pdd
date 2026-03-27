import React from "react";
import {
  BLUE_LINE_COLOR,
  AMBER_SOLID_COLOR,
  AMBER_DASHED_COLOR,
  FONT_FAMILY,
  LEGEND_FONT_SIZE,
  AXIS_LABEL_COLOR,
} from "./constants";

export interface ChartLegendProps {
  x: number;
  y: number;
}

export const ChartLegend: React.FC<ChartLegendProps> = ({ x, y }) => {
  const items = [
    { color: BLUE_LINE_COLOR, label: "Cost to generate", dash: undefined },
    { color: AMBER_DASHED_COLOR, label: "Total cost (with tech debt)", dash: "8 4" },
    { color: AMBER_SOLID_COLOR, label: "Immediate patch cost", dash: undefined },
  ];

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {items.map((item, i) => {
        const itemY = y + i * 28;
        return (
          <g key={item.label}>
            <line
              x1={x}
              y1={itemY}
              x2={x + 30}
              y2={itemY}
              stroke={item.color}
              strokeWidth={2.5}
              strokeDasharray={item.dash}
            />
            <text
              x={x + 40}
              y={itemY + 5}
              fill={AXIS_LABEL_COLOR}
              fontFamily={FONT_FAMILY}
              fontSize={LEGEND_FONT_SIZE}
            >
              {item.label}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default ChartLegend;
