import React from "react";
import {
  LEFT_PANEL_X,
  LEFT_PANEL_Y,
  LEFT_PANEL_W,
  LEFT_PANEL_H,
  RIGHT_PANEL_X,
  RIGHT_PANEL_Y,
  RIGHT_PANEL_W,
  RIGHT_PANEL_H,
  RED_BG,
  GREEN_BG,
} from "./constants";

interface SplitPanelProps {
  side: "left" | "right";
  translateX: number;
  opacity: number;
  children: React.ReactNode;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({
  side,
  translateX,
  opacity,
  children,
}) => {
  const isLeft = side === "left";
  const x = isLeft ? LEFT_PANEL_X : RIGHT_PANEL_X;
  const y = isLeft ? LEFT_PANEL_Y : RIGHT_PANEL_Y;
  const w = isLeft ? LEFT_PANEL_W : RIGHT_PANEL_W;
  const h = isLeft ? LEFT_PANEL_H : RIGHT_PANEL_H;
  const bg = isLeft ? RED_BG : GREEN_BG;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: w,
        height: h,
        transform: `translateX(${translateX}px)`,
        opacity,
        backgroundColor: bg,
        borderRadius: 12,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 28,
        padding: 40,
      }}
    >
      {children}
    </div>
  );
};

export default SplitPanel;
