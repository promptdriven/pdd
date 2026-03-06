import React from "react";
import { ARROW_COLOR, ARROW_SIZE } from "./constants";

interface ArrowIconProps {
  direction: "up" | "down";
  opacity?: number;
}

export const ArrowIcon: React.FC<ArrowIconProps> = ({
  direction,
  opacity = 1,
}) => {
  const rotation = direction === "up" ? 0 : 180;

  return (
    <svg
      width={ARROW_SIZE}
      height={ARROW_SIZE}
      viewBox="0 0 24 24"
      fill="none"
      style={{
        opacity,
        transform: `rotate(${rotation}deg)`,
        flexShrink: 0,
      }}
    >
      <path
        d="M12 4L12 20M12 4L6 10M12 4L18 10"
        stroke={ARROW_COLOR}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
};

export default ArrowIcon;
