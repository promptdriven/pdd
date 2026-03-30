import React from "react";
import { interpolate, useCurrentFrame } from "remotion";
import {
  LEGEND_ITEMS,
  BLUE_LINE_START,
  AMBER_SOLID_START,
  DASHED_LINE_START,
} from "./constants";

const LEGEND_X = 1400;
const LEGEND_Y = 60;
const LEGEND_ITEM_HEIGHT = 30;
const LEGEND_SWATCH_WIDTH = 32;

export const Legend: React.FC = () => {
  const frame = useCurrentFrame();

  // Each legend item appears when its corresponding line starts drawing
  const appearFrames = [BLUE_LINE_START, AMBER_SOLID_START, DASHED_LINE_START];

  return (
    <div
      style={{
        position: "absolute",
        top: LEGEND_Y,
        left: LEGEND_X,
        display: "flex",
        flexDirection: "column",
        gap: 8,
      }}
    >
      {LEGEND_ITEMS.map((item, idx) => {
        const opacity = interpolate(
          frame,
          [appearFrames[idx], appearFrames[idx] + 20],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        return (
          <div
            key={item.label}
            style={{
              display: "flex",
              alignItems: "center",
              gap: 10,
              opacity,
              height: LEGEND_ITEM_HEIGHT,
            }}
          >
            {/* Swatch line */}
            <svg width={LEGEND_SWATCH_WIDTH} height={4}>
              <line
                x1={0}
                y1={2}
                x2={LEGEND_SWATCH_WIDTH}
                y2={2}
                stroke={item.color}
                strokeWidth={3}
                strokeDasharray={item.dashed ? "8 6" : "none"}
              />
            </svg>
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontSize: 14,
                fontWeight: 600,
                color: item.color,
                whiteSpace: "nowrap",
              }}
            >
              {item.label}
            </span>
          </div>
        );
      })}
    </div>
  );
};

export default Legend;
