import React from "react";
import { COLORS } from "./constants";

/**
 * Renders the mold cross-section (metallic, industrial) with small
 * plastic parts below it. The mold is the focus; parts are secondary
 * and intentionally NOT glowing.
 */
export const MoldScene: React.FC = () => {
  return (
    <svg
      width="400"
      height="420"
      viewBox="0 0 400 420"
      style={{
        position: "absolute",
        left: "50%",
        top: "46%",
        transform: "translate(-50%, -50%)",
      }}
    >
      <defs>
        {/* Metallic gradient for mold body */}
        <linearGradient id="moldMetalGrad" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={COLORS.MOLD_METALLIC_LIGHT} />
          <stop offset="50%" stopColor={COLORS.MOLD_BODY} />
          <stop offset="100%" stopColor={COLORS.MOLD_METALLIC_DARK} />
        </linearGradient>
        {/* Metallic edge highlight */}
        <linearGradient id="moldEdgeGrad" x1="0" y1="0" x2="1" y2="0">
          <stop offset="0%" stopColor="#9aaaba" />
          <stop offset="50%" stopColor={COLORS.MOLD_EDGE} />
          <stop offset="100%" stopColor="#6a7a8a" />
        </linearGradient>
        {/* Drop shadow */}
        <filter id="moldSceneShadow" x="-10%" y="-10%" width="120%" height="120%">
          <feDropShadow
            dx="3"
            dy="4"
            stdDeviation="5"
            floodColor="#000"
            floodOpacity="0.5"
          />
        </filter>
      </defs>

      {/* === MOLD (centered, upper portion) === */}
      <g filter="url(#moldSceneShadow)">
        {/* Top mold half */}
        <rect
          x="60"
          y="60"
          width="280"
          height="80"
          rx="6"
          fill="url(#moldMetalGrad)"
          stroke={COLORS.MOLD_EDGE}
          strokeWidth="2"
        />
        {/* Top cavity indent */}
        <rect
          x="140"
          y="110"
          width="120"
          height="30"
          rx="6"
          fill={COLORS.MOLD_CAVITY}
        />

        {/* Bottom mold half */}
        <rect
          x="60"
          y="155"
          width="280"
          height="80"
          rx="6"
          fill="url(#moldMetalGrad)"
          stroke={COLORS.MOLD_EDGE}
          strokeWidth="2"
        />
        {/* Bottom cavity indent */}
        <rect
          x="140"
          y="155"
          width="120"
          height="30"
          rx="6"
          fill={COLORS.MOLD_CAVITY}
        />

        {/* Bolts / detail marks on mold */}
        <circle cx="85" cy="100" r="6" fill={COLORS.MOLD_METALLIC_DARK} />
        <circle cx="315" cy="100" r="6" fill={COLORS.MOLD_METALLIC_DARK} />
        <circle cx="85" cy="195" r="6" fill={COLORS.MOLD_METALLIC_DARK} />
        <circle cx="315" cy="195" r="6" fill={COLORS.MOLD_METALLIC_DARK} />

        {/* Parting line */}
        <line
          x1="60"
          y1="147"
          x2="340"
          y2="147"
          stroke={COLORS.MOLD_METALLIC_DARK}
          strokeWidth="1"
          strokeDasharray="4 3"
        />
      </g>

      {/* === PARTS (below mold, small, dim, NOT glowing) === */}
      <g opacity="0.6">
        {/* Part 1 */}
        <rect
          x="110"
          y="290"
          width="60"
          height="30"
          rx="8"
          fill={COLORS.PART_AMBER_DIM}
        />
        {/* Part 2 */}
        <rect
          x="195"
          y="295"
          width="55"
          height="28"
          rx="8"
          fill={COLORS.PART_AMBER_DIM}
        />
        {/* Part 3 */}
        <rect
          x="150"
          y="335"
          width="65"
          height="32"
          rx="8"
          fill={COLORS.PART_AMBER_DIM}
        />
      </g>
    </svg>
  );
};
