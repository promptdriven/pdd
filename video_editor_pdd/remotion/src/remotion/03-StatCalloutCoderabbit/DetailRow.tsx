import React from "react";
import { DETAIL_FONT_SIZE, ICON_SIZE } from "./constants";

interface DetailRowProps {
  icon: "error" | "warning";
  text: string;
  color: string;
  opacity: number;
  translateX: number;
}

const ErrorIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 24 24"
    fill="none"
    style={{ flexShrink: 0 }}
  >
    <circle cx="12" cy="12" r="10" stroke={color} strokeWidth="2" />
    <line x1="12" y1="8" x2="12" y2="13" stroke={color} strokeWidth="2" strokeLinecap="round" />
    <circle cx="12" cy="16.5" r="1.2" fill={color} />
  </svg>
);

const WarningIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 24 24"
    fill="none"
    style={{ flexShrink: 0 }}
  >
    <path
      d="M12 2L1 21h22L12 2z"
      stroke={color}
      strokeWidth="2"
      strokeLinejoin="round"
    />
    <line x1="12" y1="10" x2="12" y2="15" stroke={color} strokeWidth="2" strokeLinecap="round" />
    <circle cx="12" cy="18" r="1.2" fill={color} />
  </svg>
);

export const DetailRow: React.FC<DetailRowProps> = ({
  icon,
  text,
  color,
  opacity,
  translateX,
}) => {
  return (
    <div
      style={{
        display: "flex",
        flexDirection: "row",
        alignItems: "center",
        gap: 10,
        opacity,
        transform: `translateX(${translateX}px)`,
      }}
    >
      {icon === "error" ? (
        <ErrorIcon color={color} size={ICON_SIZE} />
      ) : (
        <WarningIcon color={color} size={ICON_SIZE} />
      )}
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 600,
          fontSize: DETAIL_FONT_SIZE,
          color,
          lineHeight: 1.4,
        }}
      >
        {text}
      </span>
    </div>
  );
};

export default DetailRow;
