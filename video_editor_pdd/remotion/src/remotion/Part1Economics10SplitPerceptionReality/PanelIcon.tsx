import React from "react";

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
        // Simplified thumbs-up silhouette
        <g fill={color}>
          <path d="M52 28C52 28 56 16 64 16C72 16 72 28 72 28V44H88C92.4 44 96 47.6 96 52L90 88C89 92 86 96 82 96H44V48L52 28Z" />
          <rect x="24" y="48" width="16" height="48" rx="4" />
        </g>
      ) : (
        // Simplified stopwatch silhouette
        <g fill={color}>
          {/* Watch body */}
          <circle cx="60" cy="66" r="40" />
          {/* Top button */}
          <rect x="54" y="14" width="12" height="16" rx="3" />
          {/* Side button */}
          <rect x="88" y="38" width="14" height="8" rx="2" transform="rotate(-30 88 38)" />
          {/* Clock hands (cutout effect via darker fill) */}
          <line x1="60" y1="66" x2="60" y2="42" stroke="#0A1628" strokeWidth="4" strokeLinecap="round" />
          <line x1="60" y1="66" x2="78" y2="66" stroke="#0A1628" strokeWidth="3" strokeLinecap="round" />
          {/* Center dot */}
          <circle cx="60" cy="66" r="4" fill="#0A1628" />
        </g>
      )}
    </svg>
  );
};

export default PanelIcon;
