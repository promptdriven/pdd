import React from "react";
import { RESULT_WIDTH, RESULT_HEIGHT, PILLAR_BORDER_RADIUS, RESULT_FONT_SIZE, RESULT_GLOW } from "./constants";

interface ResultBoxProps {
  opacity: number;
}

export const ResultBox: React.FC<ResultBoxProps> = ({ opacity }) => {
  return (
    <div
      style={{
        width: RESULT_WIDTH,
        height: RESULT_HEIGHT,
        borderRadius: PILLAR_BORDER_RADIUS,
        backgroundColor: "rgba(255, 255, 255, 0.08)",
        border: "2px solid #FFFFFF",
        boxShadow: RESULT_GLOW,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity,
        flexShrink: 0,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: RESULT_FONT_SIZE,
          color: "#FFFFFF",
          lineHeight: 1,
          textAlign: "center",
        }}
      >
        Complete Specification
      </div>
    </div>
  );
};

export default ResultBox;
