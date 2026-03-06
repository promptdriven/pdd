import React from "react";

interface NeedleIconProps {
  color: string;
  size: number;
  opacity: number;
}

export const NeedleIcon: React.FC<NeedleIconProps> = ({ color, size, opacity }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 64 64"
      fill="none"
      style={{ opacity }}
    >
      {/* Needle body — diagonal */}
      <line
        x1="14"
        y1="50"
        x2="50"
        y2="14"
        stroke={color}
        strokeWidth={2.5}
        strokeLinecap="round"
      />
      {/* Needle eye */}
      <ellipse
        cx="48"
        cy="16"
        rx="3"
        ry="5"
        transform="rotate(-45 48 16)"
        stroke={color}
        strokeWidth={1.8}
        fill="none"
      />
      {/* Thread trailing from eye */}
      <path
        d="M52 12 Q58 6 56 2 Q54 -1 60 4"
        stroke={color}
        strokeWidth={1.5}
        strokeLinecap="round"
        fill="none"
        opacity={0.6}
      />
      {/* Criss-cross stitching — three X marks */}
      <line x1="22" y1="38" x2="28" y2="44" stroke={color} strokeWidth={1.8} strokeLinecap="round" />
      <line x1="28" y1="38" x2="22" y2="44" stroke={color} strokeWidth={1.8} strokeLinecap="round" />

      <line x1="30" y1="30" x2="36" y2="36" stroke={color} strokeWidth={1.8} strokeLinecap="round" />
      <line x1="36" y1="30" x2="30" y2="36" stroke={color} strokeWidth={1.8} strokeLinecap="round" />

      <line x1="38" y1="22" x2="44" y2="28" stroke={color} strokeWidth={1.8} strokeLinecap="round" />
      <line x1="44" y1="22" x2="38" y2="28" stroke={color} strokeWidth={1.8} strokeLinecap="round" />

      {/* Fabric tear line */}
      <path
        d="M18 48 Q20 42 24 40 Q28 38 32 34 Q36 30 38 26 Q40 22 44 20"
        stroke={color}
        strokeWidth={1}
        strokeLinecap="round"
        fill="none"
        opacity={0.4}
        strokeDasharray="3 3"
      />
    </svg>
  );
};

export default NeedleIcon;
