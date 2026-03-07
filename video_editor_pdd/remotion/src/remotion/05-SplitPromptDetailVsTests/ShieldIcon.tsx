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
        d="M60 8 L100 28 V64 C100 88 76 108 60 114 C44 108 20 88 20 64 V28 Z"
        stroke={color}
        strokeWidth="3"
        fill="none"
      />
      {/* Checkmark 1 (top) */}
      <polyline
        points="42,50 52,60 72,40"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      {/* Checkmark 2 (middle) */}
      <polyline
        points="42,68 52,78 72,58"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      {/* Checkmark 3 (bottom) */}
      <polyline
        points="42,86 52,96 72,76"
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
