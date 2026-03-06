import React from "react";

interface RefreshCycleIconProps {
  color: string;
  size: number;
  opacity: number;
}

/**
 * Refresh cycle loop icon with a checkmark — represents the PDD generation approach.
 */
export const RefreshCycleIcon: React.FC<RefreshCycleIconProps> = ({ color, size, opacity }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 100 100"
      fill="none"
      style={{ opacity }}
    >
      {/* Circular arrow loop */}
      <path
        d="M 50 15 A 35 35 0 1 1 20 65"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        fill="none"
      />
      {/* Arrow head */}
      <polygon
        points="14,55 20,68 28,58"
        fill={color}
      />
      {/* Second arc for double-loop feel */}
      <path
        d="M 50 85 A 35 35 0 0 1 80 35"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        fill="none"
        opacity={0.5}
      />
      {/* Arrow head on second arc */}
      <polygon
        points="86,45 80,32 72,42"
        fill={color}
        opacity={0.5}
      />
      {/* Checkmark in center */}
      <polyline
        points="38,52 46,60 62,40"
        stroke={color}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
    </svg>
  );
};

export default RefreshCycleIcon;
