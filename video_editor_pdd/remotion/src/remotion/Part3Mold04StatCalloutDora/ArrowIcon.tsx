import React from "react";

interface ArrowIconProps {
  direction: "up" | "down";
  color: string;
  size: number;
}

export const ArrowIcon: React.FC<ArrowIconProps> = ({ direction, color, size }) => {
  const rotation = direction === "down" ? 180 : 0;

  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 24 24"
      fill="none"
      style={{
        transform: `rotate(${rotation}deg)`,
        flexShrink: 0,
        marginRight: 12,
      }}
    >
      {/* Chevron arrow pointing up */}
      <path
        d="M4 16L12 8L20 16"
        stroke={color}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
};

export default ArrowIcon;
