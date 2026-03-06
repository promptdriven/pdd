import React from "react";

export const ErrorIcon: React.FC<{ color: string; size?: number }> = ({
  color,
  size = 18,
}) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 24 24"
      fill="none"
      style={{ display: "inline-block", verticalAlign: "middle", marginRight: 8, flexShrink: 0 }}
    >
      <circle cx="12" cy="12" r="10" fill="none" stroke={color} strokeWidth={2} />
      <line x1="8" y1="8" x2="16" y2="16" stroke={color} strokeWidth={2} strokeLinecap="round" />
      <line x1="16" y1="8" x2="8" y2="16" stroke={color} strokeWidth={2} strokeLinecap="round" />
    </svg>
  );
};

export default ErrorIcon;
