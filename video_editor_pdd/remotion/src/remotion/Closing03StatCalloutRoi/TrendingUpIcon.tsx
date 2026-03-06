import React from "react";

interface TrendingUpIconProps {
  color: string;
  size: number;
}

export const TrendingUpIcon: React.FC<TrendingUpIconProps> = ({ color, size }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 24 24"
      fill="none"
      xmlns="http://www.w3.org/2000/svg"
      style={{ marginRight: 8, flexShrink: 0 }}
    >
      <polyline
        points="23 6 13.5 15.5 8.5 10.5 1 18"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
      <polyline
        points="17 6 23 6 23 12"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
};

export default TrendingUpIcon;
