import React from "react";

interface MoldIconProps {
  color: string;
  size: number;
  opacity: number;
}

export const MoldIcon: React.FC<MoldIconProps> = ({
  color,
  size,
  opacity,
}) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 90 90"
      fill="none"
      style={{ opacity }}
    >
      {/* Outer mold frame (top half) */}
      <path
        d="M 15 45 L 15 18 Q 15 12 21 12 L 69 12 Q 75 12 75 18 L 75 45"
        stroke={color}
        strokeWidth={3}
        fill="none"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
      {/* Outer mold frame (bottom half) */}
      <path
        d="M 15 45 L 15 72 Q 15 78 21 78 L 69 78 Q 75 78 75 72 L 75 45"
        stroke={color}
        strokeWidth={3}
        fill="none"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
      {/* Mold cavity (inner shape — clean rectangle) */}
      <rect
        x={28}
        y={28}
        width={34}
        height={34}
        rx={4}
        stroke={color}
        strokeWidth={2}
        fill={color}
        fillOpacity={0.12}
      />
      {/* Parting line */}
      <line
        x1={12}
        y1={45}
        x2={78}
        y2={45}
        stroke={color}
        strokeWidth={1.5}
        strokeDasharray="6 4"
      />
      {/* Registration pins */}
      <circle cx={20} cy={20} r={3} fill={color} fillOpacity={0.4} />
      <circle cx={70} cy={20} r={3} fill={color} fillOpacity={0.4} />
      <circle cx={20} cy={70} r={3} fill={color} fillOpacity={0.4} />
      <circle cx={70} cy={70} r={3} fill={color} fillOpacity={0.4} />
    </svg>
  );
};

export default MoldIcon;
