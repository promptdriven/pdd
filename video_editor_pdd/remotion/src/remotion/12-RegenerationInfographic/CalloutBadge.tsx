import React from "react";
import { GREEN, FONT_FAMILY } from "./constants";

interface CalloutBadgeProps {
  translateX: number;
  opacity: number;
}

export const CalloutBadge: React.FC<CalloutBadgeProps> = ({
  translateX,
  opacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        right: 120,
        top: 130,
        opacity,
        transform: `translateX(${translateX}px)`,
      }}
    >
      <div
        style={{
          display: "inline-block",
          padding: "10px 24px",
          backgroundColor: `${GREEN}33`,
          border: `1.5px solid ${GREEN}80`,
          borderRadius: 28,
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: 18,
          color: GREEN,
          whiteSpace: "nowrap",
          boxShadow: `0 0 20px ${GREEN}20`,
        }}
      >
        89% accuracy with NL context — MIT, 2024
      </div>
    </div>
  );
};
