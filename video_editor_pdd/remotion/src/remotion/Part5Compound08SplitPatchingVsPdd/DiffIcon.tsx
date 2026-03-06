import React from "react";

interface DiffIconProps {
  color: string;
  size: number;
  opacity: number;
}

/**
 * Code diff icon with layered edit strikethroughs — represents the patching approach.
 */
export const DiffIcon: React.FC<DiffIconProps> = ({ color, size, opacity }) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 100 100"
      fill="none"
      style={{ opacity }}
    >
      {/* Document outline */}
      <rect
        x="15"
        y="8"
        width="70"
        height="84"
        rx="6"
        stroke={color}
        strokeWidth="3"
        fill="none"
      />
      {/* Code lines */}
      <line x1="28" y1="28" x2="72" y2="28" stroke={color} strokeWidth="3" />
      <line x1="28" y1="40" x2="65" y2="40" stroke={color} strokeWidth="3" />
      <line x1="28" y1="52" x2="70" y2="52" stroke={color} strokeWidth="3" />
      <line x1="28" y1="64" x2="58" y2="64" stroke={color} strokeWidth="3" />
      <line x1="28" y1="76" x2="68" y2="76" stroke={color} strokeWidth="3" />

      {/* Strikethrough edits (red diff marks) */}
      <line x1="25" y1="32" x2="75" y2="24" stroke={color} strokeWidth="2.5" opacity={0.7} />
      <line x1="25" y1="56" x2="73" y2="48" stroke={color} strokeWidth="2.5" opacity={0.7} />
      <line x1="25" y1="80" x2="71" y2="72" stroke={color} strokeWidth="2.5" opacity={0.7} />

      {/* Plus/minus symbols */}
      <text x="78" y="32" fill={color} fontSize="14" fontWeight="bold" fontFamily="Inter, sans-serif">−</text>
      <text x="78" y="44" fill={color} fontSize="14" fontWeight="bold" fontFamily="Inter, sans-serif">+</text>
      <text x="78" y="56" fill={color} fontSize="14" fontWeight="bold" fontFamily="Inter, sans-serif">−</text>
    </svg>
  );
};

export default DiffIcon;
