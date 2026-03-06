import React from "react";

export const CautionIcon: React.FC<{ color: string; size?: number }> = ({
  color,
  size = 16,
}) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 24 24"
      fill="none"
      style={{ display: "inline-block", verticalAlign: "middle", marginRight: 6 }}
    >
      <path
        d="M12 2L1 21h22L12 2z"
        fill="none"
        stroke={color}
        strokeWidth={2}
        strokeLinejoin="round"
      />
      <line x1="12" y1="9" x2="12" y2="15" stroke={color} strokeWidth={2} strokeLinecap="round" />
      <circle cx="12" cy="18" r="1" fill={color} />
    </svg>
  );
};

export default CautionIcon;
