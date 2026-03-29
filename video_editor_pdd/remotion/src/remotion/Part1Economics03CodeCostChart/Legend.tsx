import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  BLUE_LINE_START,
  AMBER_SOLID_START,
  DASHED_START,
} from "./constants";

interface LegendItemProps {
  label: string;
  color: string;
  dashed?: boolean;
  opacity: number;
}

const LegendItem: React.FC<LegendItemProps> = ({
  label,
  color,
  dashed = false,
  opacity,
}) => (
  <div
    style={{
      display: "flex",
      alignItems: "center",
      gap: 10,
      opacity,
    }}
  >
    <svg width={30} height={4}>
      <line
        x1={0}
        y1={2}
        x2={30}
        y2={2}
        stroke={color}
        strokeWidth={3}
        strokeDasharray={dashed ? "8 6" : "none"}
      />
    </svg>
    <span
      style={{
        color,
        fontFamily: "Inter, sans-serif",
        fontSize: 14,
        fontWeight: 600,
      }}
    >
      {label}
    </span>
  </div>
);

export const ChartLegend: React.FC = () => {
  const frame = useCurrentFrame();

  const blueOpacity = interpolate(frame, [BLUE_LINE_START, BLUE_LINE_START + 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const amberSolidOpacity = interpolate(
    frame,
    [AMBER_SOLID_START, AMBER_SOLID_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const amberDashedOpacity = interpolate(
    frame,
    [DASHED_START, DASHED_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        right: 80,
        top: 40,
        display: "flex",
        flexDirection: "column",
        gap: 8,
      }}
    >
      <LegendItem
        label="Cost to generate"
        color={BLUE_LINE_COLOR}
        opacity={blueOpacity}
      />
      <LegendItem
        label="Immediate patch cost"
        color={AMBER_LINE_COLOR}
        opacity={amberSolidOpacity}
      />
      <LegendItem
        label="Total cost (with debt)"
        color={AMBER_LINE_COLOR}
        dashed
        opacity={amberDashedOpacity}
      />
    </div>
  );
};

export default ChartLegend;
