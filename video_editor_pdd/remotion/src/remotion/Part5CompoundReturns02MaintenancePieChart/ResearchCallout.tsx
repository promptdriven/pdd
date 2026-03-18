import React from "react";
import { useCurrentFrame, Easing, interpolate } from "remotion";
import {
  CARD_BG,
  CARD_BORDER,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  TEXT_MUTED,
  AMBER,
  CALLOUT_WIDTH,
  CALLOUT_HEIGHT,
} from "./constants";

// ── Simple SVG Icons ────────────────────────────────────────────────

const BarChartIcon: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <svg width={20} height={20} viewBox="0 0 20 20" style={{ opacity }}>
    <rect x={2} y={10} width={4} height={8} rx={1} fill={color} />
    <rect x={8} y={6} width={4} height={12} rx={1} fill={color} />
    <rect x={14} y={2} width={4} height={16} rx={1} fill={color} />
  </svg>
);

const ClockIcon: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <svg width={20} height={20} viewBox="0 0 20 20" style={{ opacity }}>
    <circle
      cx={10}
      cy={10}
      r={8}
      fill="none"
      stroke={color}
      strokeWidth={1.5}
    />
    <line
      x1={10}
      y1={10}
      x2={10}
      y2={5}
      stroke={color}
      strokeWidth={1.5}
      strokeLinecap="round"
    />
    <line
      x1={10}
      y1={10}
      x2={14}
      y2={10}
      stroke={color}
      strokeWidth={1.5}
      strokeLinecap="round"
    />
  </svg>
);

// ── Types ───────────────────────────────────────────────────────────

interface ResearchCalloutProps {
  x: number;
  y: number;
  icon: "bar_chart" | "clock";
  mainText: string;
  subText: string;
  source: string;
  slideStartFrame: number;
  slideDuration: number;
  pulseStartFrame: number;
  pulseDuration: number;
}

// ── Component ───────────────────────────────────────────────────────

export const ResearchCallout: React.FC<ResearchCalloutProps> = ({
  x,
  y,
  icon,
  mainText,
  subText,
  source,
  slideStartFrame,
  slideDuration,
  pulseStartFrame,
  pulseDuration,
}) => {
  const frame = useCurrentFrame();

  // Slide-in from right
  const slideProgress = interpolate(
    frame,
    [slideStartFrame, slideStartFrame + slideDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const translateX = interpolate(slideProgress, [0, 1], [30, 0]);
  const opacity = slideProgress;

  // Pulse effect on main text
  const pulseScale = interpolate(
    frame,
    [
      pulseStartFrame,
      pulseStartFrame + pulseDuration / 2,
      pulseStartFrame + pulseDuration,
    ],
    [1, 1.05, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.bezier(0.37, 0, 0.63, 1), // sine-like
    }
  );

  const IconComponent = icon === "bar_chart" ? BarChartIcon : ClockIcon;

  return (
    <div
      style={{
        position: "absolute",
        left: x - CALLOUT_WIDTH / 2,
        top: y - CALLOUT_HEIGHT / 2,
        width: CALLOUT_WIDTH,
        height: CALLOUT_HEIGHT,
        backgroundColor: `rgba(30, 41, 59, 0.4)`,
        border: `1px solid rgba(51, 65, 85, 0.2)`,
        borderRadius: 8,
        display: "flex",
        flexDirection: "row",
        alignItems: "center",
        padding: "12px 16px",
        gap: 12,
        transform: `translateX(${translateX}px)`,
        opacity,
        boxSizing: "border-box",
      }}
    >
      {/* Icon */}
      <div style={{ flexShrink: 0 }}>
        <IconComponent color={AMBER} opacity={0.5} />
      </div>

      {/* Text content */}
      <div style={{ display: "flex", flexDirection: "column", gap: 2 }}>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 16,
            fontWeight: 600,
            color: TEXT_PRIMARY,
            transform: `scale(${pulseScale})`,
            transformOrigin: "left center",
            whiteSpace: "nowrap",
          }}
        >
          {mainText}
        </div>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 11,
            color: TEXT_SECONDARY,
            opacity: 0.5,
            whiteSpace: "nowrap",
          }}
        >
          {subText}
        </div>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 9,
            color: TEXT_MUTED,
            opacity: 0.3,
            whiteSpace: "nowrap",
          }}
        >
          {source}
        </div>
      </div>
    </div>
  );
};

export default ResearchCallout;
