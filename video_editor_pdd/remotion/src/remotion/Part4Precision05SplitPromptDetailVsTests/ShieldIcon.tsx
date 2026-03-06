import React from "react";

interface ShieldIconProps {
  color: string;
  size: number;
  opacity: number;
}

export const ShieldIcon: React.FC<ShieldIconProps> = ({
  color,
  size,
  opacity,
}) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 120 120"
      fill="none"
      style={{ opacity }}
    >
      {/* Shield outline */}
      <path
        d="M60 8 L100 28 L100 60 C100 85 80 105 60 112 C40 105 20 85 20 60 L20 28 Z"
        stroke={color}
        strokeWidth="3"
        fill="none"
      />
      {/* Stacked checkmarks */}
      <polyline
        points="40,50 52,62 78,36"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      <polyline
        points="40,68 52,80 78,54"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      <polyline
        points="40,86 52,98 78,72"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
    </svg>
  );
};

export default ShieldIcon;
