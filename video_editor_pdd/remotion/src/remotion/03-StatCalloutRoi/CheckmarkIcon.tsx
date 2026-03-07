import React from "react";

interface CheckmarkIconProps {
  color: string;
  size: number;
}

export const CheckmarkIcon: React.FC<CheckmarkIconProps> = ({ color, size }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 24 24"
      fill="none"
      xmlns="http://www.w3.org/2000/svg"
      style={{ marginRight: 8, flexShrink: 0 }}
    >
      <path
        d="M20 6L9 17L4 12"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
};

export default CheckmarkIcon;
