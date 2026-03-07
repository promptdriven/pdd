import React from "react";

interface DocumentIconProps {
  color: string;
  size: number;
  opacity: number;
}

export const DocumentIcon: React.FC<DocumentIconProps> = ({
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
      {/* Document body */}
      <rect
        x="24"
        y="8"
        width="72"
        height="104"
        rx="6"
        stroke={color}
        strokeWidth="3"
        fill="none"
      />
      {/* Folded corner */}
      <path d="M72 8 L96 32 L72 32 Z" stroke={color} strokeWidth="2" fill="none" />
      {/* Text lines */}
      <line x1="36" y1="48" x2="84" y2="48" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="36" y1="60" x2="78" y2="60" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="36" y1="72" x2="82" y2="72" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="36" y1="84" x2="68" y2="84" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="36" y1="96" x2="74" y2="96" stroke={color} strokeWidth="3" strokeLinecap="round" />
    </svg>
  );
};

export default DocumentIcon;
