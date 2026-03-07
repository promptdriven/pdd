import React from "react";
import { DIVIDER_X, LEFT_PANEL_Y, LEFT_PANEL_H, WHITE } from "./constants";

interface VerticalDividerProps {
  opacity: number;
}

export const VerticalDivider: React.FC<VerticalDividerProps> = ({ opacity }) => {
  return (
    <div
      style={{
        position: "absolute",
        left: DIVIDER_X - 1,
        top: LEFT_PANEL_Y,
        width: 2,
        height: LEFT_PANEL_H,
        backgroundColor: WHITE,
        opacity,
        boxShadow: `0 0 12px 4px rgba(255, 255, 255, 0.3)`,
      }}
    />
  );
};

export default VerticalDivider;
