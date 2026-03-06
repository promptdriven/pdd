import React from "react";

interface MoldIconProps {
  color: string;
  size: number;
  opacity: number;
}

export const MoldIcon: React.FC<MoldIconProps> = ({ color, size, opacity }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 64 64"
      fill="none"
      style={{ opacity }}
    >
      {/* Mold top half — open cavity shape */}
      <path
        d="M8 30 L8 10 Q8 6 12 6 L52 6 Q56 6 56 10 L56 30"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      {/* Top cavity indent */}
      <path
        d="M18 30 L18 20 Q18 14 32 14 Q46 14 46 20 L46 30"
        stroke={color}
        strokeWidth={1.8}
        strokeLinecap="round"
        fill="none"
        opacity={0.5}
      />

      {/* Mold bottom half — matching shape */}
      <path
        d="M8 34 L8 54 Q8 58 12 58 L52 58 Q56 58 56 54 L56 34"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
        fill="none"
      />
      {/* Bottom cavity protrusion */}
      <path
        d="M18 34 L18 44 Q18 50 32 50 Q46 50 46 44 L46 34"
        stroke={color}
        strokeWidth={1.8}
        strokeLinecap="round"
        fill="none"
        opacity={0.5}
      />

      {/* Seam line between halves */}
      <line
        x1="4"
        y1="32"
        x2="60"
        y2="32"
        stroke={color}
        strokeWidth={1}
        opacity={0.4}
        strokeDasharray="4 3"
      />

      {/* Small alignment pins */}
      <circle cx="12" cy="30" r="2" fill={color} opacity={0.5} />
      <circle cx="12" cy="34" r="2" fill={color} opacity={0.5} />
      <circle cx="52" cy="30" r="2" fill={color} opacity={0.5} />
      <circle cx="52" cy="34" r="2" fill={color} opacity={0.5} />
    </svg>
  );
};

export default MoldIcon;
