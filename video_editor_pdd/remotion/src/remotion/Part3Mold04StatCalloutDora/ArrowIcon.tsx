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
      <path
        d="M12 4L12 20M12 4L6 10M12 4L18 10"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
};

export default ArrowIcon;
