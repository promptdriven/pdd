import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from "remotion";
import {
  LEFT_PANEL,
  RIGHT_PANEL,
  GREEN,
  GREEN_MUTED,
  GREEN_BG,
  RED,
  RED_MUTED,
  RED_BG,
  FONT_FAMILY,
  HEADER_SIZE,
  STAT_SIZE,
  DESCRIPTOR_SIZE,
  ARROW_SIZE,
  PANEL_SLIDE_IN_START,
  PANEL_SLIDE_IN_END,
  PANEL_SLIDE_OUT_START,
  PANEL_SLIDE_OUT_END,
  PANEL_SPRING_DAMPING,
  PANEL_SPRING_STIFFNESS,
  LEFT_HEADER_START,
  LEFT_HEADER_END,
  LEFT_STAT_START,
  LEFT_STAT_END,
  RIGHT_HEADER_START,
  RIGHT_HEADER_END,
  RIGHT_STAT_START,
  RIGHT_STAT_END,
} from "./constants";

interface SplitPanelProps {
  side: "left" | "right";
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side }) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const isLeft = side === "left";

  const panel = isLeft ? LEFT_PANEL : RIGHT_PANEL;
  const color = isLeft ? GREEN : RED;
  const mutedColor = isLeft ? GREEN_MUTED : RED_MUTED;
  const bgColor = isLeft ? GREEN_BG : RED_BG;
  const headerText = isLeft ? "PERCEPTION" : "REALITY";
  const statValue = isLeft ? 20 : 19;
  const statPrefix = isLeft ? "+" : "";
  const descriptor = isLeft ? "faster (self-reported)" : "slower (measured)";
  const arrowDirection = isLeft ? "up" : "down";

  const headerStart = isLeft ? LEFT_HEADER_START : RIGHT_HEADER_START;
  const headerEnd = isLeft ? LEFT_HEADER_END : RIGHT_HEADER_END;
  const statStart = isLeft ? LEFT_STAT_START : RIGHT_STAT_START;
  const statEnd = isLeft ? LEFT_STAT_END : RIGHT_STAT_END;

  // Panel slide using spring
  const slideInProgress = spring({
    frame: frame - PANEL_SLIDE_IN_START,
    fps,
    config: {
      damping: PANEL_SPRING_DAMPING,
      stiffness: PANEL_SPRING_STIFFNESS,
    },
  });

  // Slide out using easeInCubic
  const slideOutProgress = interpolate(
    frame,
    [PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) },
  );

  const slideOffset = isLeft ? -960 : 960;
  const translateX =
    slideOffset * (1 - slideInProgress) + slideOffset * slideOutProgress;

  // Opacity
  const opacity = interpolate(
    frame,
    [PANEL_SLIDE_IN_START, PANEL_SLIDE_IN_END, PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Header fade
  const headerOpacity = interpolate(
    frame,
    [headerStart, headerEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
  );

  // Stat counter animate
  const statProgress = interpolate(
    frame,
    [statStart, statEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) },
  );
  const displayValue = Math.round(statValue * statProgress);

  // Descriptor opacity (appears with stat)
  const descriptorOpacity = interpolate(
    frame,
    [statStart + 5, statEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
  );

  // Arrow chevron path
  const chevronPath =
    arrowDirection === "up"
      ? `M ${ARROW_SIZE * 0.2} ${ARROW_SIZE * 0.65} L ${ARROW_SIZE * 0.5} ${ARROW_SIZE * 0.25} L ${ARROW_SIZE * 0.8} ${ARROW_SIZE * 0.65}`
      : `M ${ARROW_SIZE * 0.2} ${ARROW_SIZE * 0.35} L ${ARROW_SIZE * 0.5} ${ARROW_SIZE * 0.75} L ${ARROW_SIZE * 0.8} ${ARROW_SIZE * 0.35}`;

  // Icon — thumbs-up silhouette for left, stopwatch for right
  const iconElement = isLeft ? (
    <svg width={120} height={120} viewBox="0 0 120 120" style={{ opacity: 0.3 }}>
      {/* Simplified thumbs-up */}
      <circle cx={60} cy={40} r={20} fill={GREEN} />
      <path
        d="M45 55 Q45 45 55 45 L65 45 Q75 45 75 55 L75 85 Q75 95 65 95 L55 95 Q45 95 45 85 Z"
        fill={GREEN}
      />
      <path
        d="M75 60 L85 55 Q90 53 90 58 L90 75 Q90 80 85 78 L75 73"
        fill={GREEN}
      />
    </svg>
  ) : (
    <svg width={120} height={120} viewBox="0 0 120 120" style={{ opacity: 0.3 }}>
      {/* Simplified stopwatch */}
      <circle cx={60} cy={65} r={35} stroke={RED} strokeWidth={4} fill="none" />
      <line x1={60} y1={65} x2={60} y2={42} stroke={RED} strokeWidth={3} strokeLinecap="round" />
      <line x1={60} y1={65} x2={75} y2={65} stroke={RED} strokeWidth={3} strokeLinecap="round" />
      <rect x={55} y={22} width={10} height={10} rx={2} fill={RED} />
      <line x1={60} y1={22} x2={60} y2={30} stroke={RED} strokeWidth={3} />
    </svg>
  );

  return (
    <div
      style={{
        position: "absolute",
        left: panel.x,
        top: panel.y,
        width: panel.w,
        height: panel.h,
        transform: `translateX(${translateX}px)`,
        opacity,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 16,
      }}
    >
      {/* Semi-transparent background */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: bgColor,
          borderRadius: 16,
          border: `1px solid ${color}22`,
        }}
      />

      {/* Background icon */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          right: isLeft ? 60 : undefined,
          left: isLeft ? undefined : 60,
        }}
      >
        {iconElement}
      </div>

      {/* Header */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontWeight: 900,
          fontSize: HEADER_SIZE,
          color,
          letterSpacing: "0.15em",
          textTransform: "uppercase",
          opacity: headerOpacity,
          zIndex: 1,
        }}
      >
        {headerText}
      </div>

      {/* Arrow chevron */}
      <div style={{ opacity: headerOpacity, zIndex: 1 }}>
        <svg width={ARROW_SIZE} height={ARROW_SIZE} viewBox={`0 0 ${ARROW_SIZE} ${ARROW_SIZE}`}>
          <path
            d={chevronPath}
            stroke={color}
            strokeWidth={6}
            strokeLinecap="round"
            strokeLinejoin="round"
            fill="none"
          />
        </svg>
      </div>

      {/* Stat number */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontWeight: 900,
          fontSize: STAT_SIZE,
          color: "#FFFFFF",
          lineHeight: 1,
          opacity: statProgress > 0 ? 1 : 0,
          zIndex: 1,
        }}
      >
        {statPrefix}{displayValue}%
      </div>

      {/* Descriptor */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: DESCRIPTOR_SIZE,
          color: mutedColor,
          opacity: descriptorOpacity,
          zIndex: 1,
        }}
      >
        {descriptor}
      </div>
    </div>
  );
};

export default SplitPanel;
