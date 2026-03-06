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
        x="25"
        y="10"
        width="70"
        height="100"
        rx="6"
        stroke={color}
        strokeWidth="3"
        fill="none"
      />
      {/* Folded corner */}
      <path d="M75 10 L95 30 L75 30 Z" stroke={color} strokeWidth="2" fill="none" />
      {/* Text lines */}
      <line x1="38" y1="45" x2="82" y2="45" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="38" y1="58" x2="78" y2="58" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="38" y1="71" x2="72" y2="71" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="38" y1="84" x2="68" y2="84" stroke={color} strokeWidth="3" strokeLinecap="round" />
      <line x1="38" y1="97" x2="60" y2="97" stroke={color} strokeWidth="3" strokeLinecap="round" />
    </svg>
  );
};

export default DocumentIcon;
