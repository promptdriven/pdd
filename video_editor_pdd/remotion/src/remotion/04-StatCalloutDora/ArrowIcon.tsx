import React from "react";

interface ArrowIconProps {
  direction: "up" | "down";
  color: string;
  size: number;
}

export const ArrowIcon: React.FC<ArrowIconProps> = ({
  direction,
  color,
  size,
}) => {
  const points =
    direction === "up"
      ? "6,18 12,6 18,18" // upward chevron
      : "6,6 12,18 18,6"; // downward chevron

  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 24 24"
      fill="none"
      style={{ flexShrink: 0, marginRight: 12 }}
    >
      <polyline
        points={points}
        stroke={color}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
    </svg>
  );
};

export default ArrowIcon;
