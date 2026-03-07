import React from "react";
import { BG_COLOR } from "./constants";

interface PanelIconProps {
  type: "thumbsUp" | "stopwatch";
  color: string;
  opacity: number;
}

export const PanelIcon: React.FC<PanelIconProps> = ({ type, color, opacity }) => {
  return (
    <svg
      width={120}
      height={120}
      viewBox="0 0 120 120"
      fill="none"
      style={{ opacity }}
    >
      {type === "thumbsUp" ? (
        <g fill={color}>
          <path d="M52 28C52 28 56 16 64 16C72 16 72 28 72 28V44H88C92.4 44 96 47.6 96 52L90 88C89 92 86 96 82 96H44V48L52 28Z" />
          <rect x="24" y="48" width="16" height="48" rx="4" />
        </g>
      ) : (
        <g fill={color}>
          <circle cx="60" cy="66" r="40" />
          <rect x="54" y="14" width="12" height="16" rx="3" />
          <rect
            x="88"
            y="38"
            width="14"
            height="8"
            rx="2"
            transform="rotate(-30 88 38)"
          />
          <line
            x1="60" y1="66" x2="60" y2="42"
            stroke={BG_COLOR} strokeWidth="4" strokeLinecap="round"
          />
          <line
            x1="60" y1="66" x2="78" y2="66"
            stroke={BG_COLOR} strokeWidth="3" strokeLinecap="round"
          />
          <circle cx="60" cy="66" r="4" fill={BG_COLOR} />
        </g>
      )}
    </svg>
  );
};

export default PanelIcon;
