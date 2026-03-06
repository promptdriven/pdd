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
        <path
          d="M40 16L64 48H16L40 16Z"
          fill={color}
          stroke={color}
          strokeWidth={2}
          strokeLinejoin="round"
        />
      ) : (
        <path
          d="M40 64L16 32H64L40 64Z"
          fill={color}
          stroke={color}
          strokeWidth={2}
          strokeLinejoin="round"
        />
      )}
    </svg>
  );
};

export default ArrowIcon;
