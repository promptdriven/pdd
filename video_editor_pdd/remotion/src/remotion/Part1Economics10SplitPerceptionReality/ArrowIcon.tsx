import React from "react";
import { ARROW_SIZE } from "./constants";

interface ArrowIconProps {
  direction: "up" | "down";
  color: string;
}

export const ArrowIcon: React.FC<ArrowIconProps> = ({ direction, color }) => {
  const isUp = direction === "up";

  return (
    <svg
      width={ARROW_SIZE}
      height={ARROW_SIZE}
      viewBox="0 0 80 80"
      fill="none"
      style={{ display: "block" }}
    >
      {isUp ? (
        <polyline
          points="16,56 40,24 64,56"
          fill="none"
          stroke={color}
          strokeWidth={8}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      ) : (
        <polyline
          points="16,24 40,56 64,24"
          fill="none"
          stroke={color}
          strokeWidth={8}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      )}
    </svg>
  );
};

export default ArrowIcon;
