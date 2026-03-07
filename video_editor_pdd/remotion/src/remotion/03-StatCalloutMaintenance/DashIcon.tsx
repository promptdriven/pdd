import React from "react";

interface DashIconProps {
  color: string;
  size: number;
}

export const DashIcon: React.FC<DashIconProps> = ({ color, size }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 18 18"
      fill="none"
      style={{ marginRight: 10, flexShrink: 0 }}
    >
      <line
        x1="3"
        y1="9"
        x2="15"
        y2="9"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
      />
    </svg>
  );
};

export default DashIcon;
