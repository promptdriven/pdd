import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CENTER_X,
  CENTER_Y,
  OUTER_W,
  OUTER_H,
  INNER_H,
  NOZZLE_H,
  LABEL_FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  CONNECTOR_LINE_WIDTH,
  CONNECTOR_LINE_OPACITY,
  LABEL_FADE_FRAMES,
  REGION_GLOW_FRAMES,
  CANVAS_W,
  CANVAS_H,
} from "./constants";
import type { RegionDef } from "./constants";

interface ConnectorLabelProps {
  region: RegionDef;
}

interface LabelLayout {
  labelX: number;
  labelY: number;
  lineX1: number;
  lineY1: number;
  lineX2: number;
  lineY2: number;
  textAnchor: string;
}

const getLayout = (position: RegionDef["labelPosition"]): LabelLayout => {
  const moldLeft = CENTER_X - OUTER_W / 2;
  const moldRight = CENTER_X + OUTER_W / 2;
  const moldTop = CENTER_Y - OUTER_H / 2;
  const moldBottom = CENTER_Y + OUTER_H / 2;
  const nozzleTop = moldTop - NOZZLE_H;
  const innerBottom = CENTER_Y + INNER_H / 2 + 20;

  switch (position) {
    case "left":
      return {
        labelX: moldLeft - 80,
        labelY: CENTER_Y,
        lineX1: moldLeft - 12,
        lineY1: CENTER_Y,
        lineX2: moldLeft - 60,
        lineY2: CENTER_Y,
        textAnchor: "end",
      };
    case "top":
      return {
        labelX: CENTER_X,
        labelY: nozzleTop - 40,
        lineX1: CENTER_X,
        lineY1: nozzleTop - 4,
        lineX2: CENTER_X,
        lineY2: nozzleTop - 26,
        textAnchor: "middle",
      };
    case "bottom":
      return {
        labelX: CENTER_X,
        labelY: moldBottom + 52,
        lineX1: CENTER_X,
        lineY1: innerBottom + 8,
        lineX2: CENTER_X,
        lineY2: moldBottom + 30,
        textAnchor: "middle",
      };
  }
};

export const ConnectorLabel: React.FC<ConnectorLabelProps> = ({ region }) => {
  const frame = useCurrentFrame();
  const fadeStart = region.highlightFrame + REGION_GLOW_FRAMES / 2;

  const opacity = interpolate(
    frame,
    [fadeStart, fadeStart + LABEL_FADE_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const layout = getLayout(region.labelPosition);

  return (
    <svg
      width={CANVAS_W}
      height={CANVAS_H}
      viewBox={`0 0 ${CANVAS_W} ${CANVAS_H}`}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <g opacity={opacity}>
        {/* Connector line */}
        <line
          x1={layout.lineX1}
          y1={layout.lineY1}
          x2={layout.lineX2}
          y2={layout.lineY2}
          stroke={region.color}
          strokeWidth={CONNECTOR_LINE_WIDTH}
          opacity={CONNECTOR_LINE_OPACITY}
        />
        {/* Label text */}
        <text
          x={layout.labelX}
          y={layout.labelY}
          textAnchor={layout.textAnchor}
          dominantBaseline="middle"
          fontFamily={LABEL_FONT_FAMILY}
          fontSize={LABEL_FONT_SIZE}
          fontWeight={LABEL_FONT_WEIGHT}
          fill={region.color}
        >
          {region.label}
        </text>
      </g>
    </svg>
  );
};
