import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  ICON_SIZE,
  RED,
  RED_ICON_OPACITY,
  LEFT_HEADER_FADE_START,
  LEFT_HEADER_FADE_END,
} from "./constants";

export const DiffIcon: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LEFT_HEADER_FADE_START, LEFT_HEADER_FADE_END],
    [0, RED_ICON_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        width: ICON_SIZE,
        height: ICON_SIZE,
        opacity,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      <svg width={ICON_SIZE} height={ICON_SIZE} viewBox="0 0 100 100">
        {/* Document background */}
        <rect x={15} y={5} width={70} height={90} rx={6} fill={RED} opacity={0.15} stroke={RED} strokeWidth={2} />

        {/* Code lines with strikethroughs */}
        {/* Line 1 — original */}
        <rect x={28} y={22} width={44} height={4} rx={2} fill={RED} opacity={0.5} />
        {/* Strikethrough */}
        <line x1={26} y1={24} x2={74} y2={24} stroke={RED} strokeWidth={1.5} opacity={0.8} />

        {/* Line 2 — replacement (shifted) */}
        <rect x={32} y={32} width={36} height={4} rx={2} fill={RED} opacity={0.7} />

        {/* Line 3 — original */}
        <rect x={28} y={46} width={40} height={4} rx={2} fill={RED} opacity={0.5} />
        {/* Strikethrough */}
        <line x1={26} y1={48} x2={70} y2={48} stroke={RED} strokeWidth={1.5} opacity={0.8} />

        {/* Line 4 — replacement */}
        <rect x={32} y={56} width={30} height={4} rx={2} fill={RED} opacity={0.7} />

        {/* Line 5 — original */}
        <rect x={28} y={70} width={48} height={4} rx={2} fill={RED} opacity={0.5} />
        {/* Strikethrough */}
        <line x1={26} y1={72} x2={78} y2={72} stroke={RED} strokeWidth={1.5} opacity={0.8} />

        {/* Line 6 — replacement */}
        <rect x={32} y={80} width={28} height={4} rx={2} fill={RED} opacity={0.7} />

        {/* Plus/minus indicators */}
        <text x={22} y={36} fill={RED} fontSize={12} fontFamily="monospace" fontWeight={700}>+</text>
        <text x={22} y={60} fill={RED} fontSize={12} fontFamily="monospace" fontWeight={700}>+</text>
        <text x={22} y={84} fill={RED} fontSize={12} fontFamily="monospace" fontWeight={700}>+</text>
      </svg>
    </div>
  );
};

export default DiffIcon;
