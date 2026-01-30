import React from "react";
import { COLORS } from "./constants";

/**
 * Renders a stylized wooden chair silhouette as SVG.
 * Simple but recognizable side-view of a classic wooden chair.
 */
export const ChairSilhouette: React.FC = () => {
  return (
    <svg
      width="280"
      height="360"
      viewBox="0 0 280 360"
      style={{
        position: "absolute",
        left: "50%",
        top: "50%",
        transform: "translate(-50%, -50%)",
      }}
    >
      <defs>
        {/* Wood grain gradient */}
        <linearGradient id="woodGrain" x1="0" y1="0" x2="1" y2="0.3">
          <stop offset="0%" stopColor={COLORS.CHAIR_WOOD_LIGHT} />
          <stop offset="30%" stopColor={COLORS.CHAIR_WOOD} />
          <stop offset="60%" stopColor={COLORS.CHAIR_WOOD_DARK} />
          <stop offset="100%" stopColor={COLORS.CHAIR_WOOD} />
        </linearGradient>
        {/* Subtle shadow for depth */}
        <filter id="chairShadow" x="-5%" y="-5%" width="110%" height="110%">
          <feDropShadow
            dx="2"
            dy="3"
            stdDeviation="3"
            floodColor="#000"
            floodOpacity="0.4"
          />
        </filter>
      </defs>

      <g filter="url(#chairShadow)">
        {/* Back rest - vertical back panel */}
        <rect
          x="80"
          y="20"
          width="120"
          height="16"
          rx="4"
          fill="url(#woodGrain)"
        />
        {/* Back rest - middle slat */}
        <rect
          x="85"
          y="60"
          width="110"
          height="12"
          rx="3"
          fill="url(#woodGrain)"
        />
        {/* Back rest - lower slat */}
        <rect
          x="90"
          y="95"
          width="100"
          height="12"
          rx="3"
          fill="url(#woodGrain)"
        />

        {/* Left back leg (full height) */}
        <rect
          x="82"
          y="20"
          width="14"
          height="320"
          rx="4"
          fill="url(#woodGrain)"
        />
        {/* Right back leg (full height) */}
        <rect
          x="184"
          y="20"
          width="14"
          height="320"
          rx="4"
          fill="url(#woodGrain)"
        />

        {/* Seat surface */}
        <rect
          x="60"
          y="150"
          width="160"
          height="18"
          rx="4"
          fill="url(#woodGrain)"
        />

        {/* Left front leg */}
        <rect
          x="62"
          y="168"
          width="14"
          height="172"
          rx="4"
          fill="url(#woodGrain)"
        />
        {/* Right front leg */}
        <rect
          x="204"
          y="168"
          width="14"
          height="172"
          rx="4"
          fill="url(#woodGrain)"
        />

        {/* Front stretcher (cross-bar between front legs) */}
        <rect
          x="62"
          y="280"
          width="156"
          height="10"
          rx="3"
          fill={COLORS.CHAIR_WOOD_DARK}
        />
        {/* Side stretcher left */}
        <rect
          x="68"
          y="270"
          width="10"
          height="40"
          rx="3"
          fill={COLORS.CHAIR_WOOD_DARK}
          transform="rotate(-15, 73, 290)"
        />
        {/* Side stretcher right */}
        <rect
          x="200"
          y="270"
          width="10"
          height="40"
          rx="3"
          fill={COLORS.CHAIR_WOOD_DARK}
          transform="rotate(15, 205, 290)"
        />
      </g>
    </svg>
  );
};
