import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PANEL_RADIUS,
  PANEL_BG,
  SUBTEXT_COLOR,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

interface SplitPanelProps {
  /** Panel position and size */
  x: number;
  y: number;
  w: number;
  h: number;
  /** Background tint color */
  tintBg: string;
  /** Primary accent color */
  accentColor: string;
  /** Muted accent color for cost unit */
  mutedColor: string;
  /** Panel header (e.g. "PROMPT DETAIL") */
  header: string;
  /** Large stat number (e.g. "~2,000") */
  statValue: string;
  /** Cost unit text (e.g. "tokens per prompt") */
  costUnit: string;
  /** Subtext (e.g. "structured, precise, repeatable") */
  subtext: string;
  /** Icon component to render */
  icon: React.ReactNode;
  /** Slide translateX (animated externally) */
  translateX: number;
  /** Panel opacity (animated externally) */
  opacity: number;
  /** Header content fade-in range */
  headerFadeStart: number;
  headerFadeEnd: number;
  /** Stat fade-in range */
  statFadeStart: number;
  statFadeEnd: number;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({
  x,
  y,
  w,
  h,
  tintBg,
  accentColor,
  mutedColor,
  header,
  statValue,
  costUnit,
  subtext,
  icon,
  translateX,
  opacity,
  headerFadeStart,
  headerFadeEnd,
  statFadeStart,
  statFadeEnd,
}) => {
  const frame = useCurrentFrame();

  const headerOpacity = interpolate(
    frame,
    [headerFadeStart, headerFadeEnd, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
  );

  const statOpacity = interpolate(
    frame,
    [statFadeStart, statFadeEnd, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
  );

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: w,
        height: h,
        borderRadius: PANEL_RADIUS,
        backgroundColor: PANEL_BG,
        backdropFilter: "blur(12px)",
        WebkitBackdropFilter: "blur(12px)",
        overflow: "hidden",
        transform: `translateX(${translateX}px)`,
        opacity,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 16,
      }}
    >
      {/* Color tint overlay */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: tintBg,
          borderRadius: PANEL_RADIUS,
          pointerEvents: "none",
        }}
      />

      {/* Header */}
      <div
        style={{
          position: "relative",
          zIndex: 1,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 900,
          fontSize: 28,
          color: accentColor,
          textTransform: "uppercase",
          letterSpacing: "0.15em",
          opacity: headerOpacity,
        }}
      >
        {header}
      </div>

      {/* Icon */}
      <div style={{ position: "relative", zIndex: 1, opacity: headerOpacity }}>
        {icon}
      </div>

      {/* Stat value */}
      <div
        style={{
          position: "relative",
          zIndex: 1,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 900,
          fontSize: 80,
          color: "#FFFFFF",
          lineHeight: 1,
          opacity: statOpacity,
          textShadow: `0 4px 24px rgba(255, 255, 255, 0.15)`,
        }}
      >
        {statValue}
      </div>

      {/* Cost unit */}
      <div
        style={{
          position: "relative",
          zIndex: 1,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 500,
          fontSize: 24,
          color: mutedColor,
          opacity: statOpacity,
        }}
      >
        {costUnit}
      </div>

      {/* Subtext */}
      <div
        style={{
          position: "relative",
          zIndex: 1,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 400,
          fontSize: 18,
          color: SUBTEXT_COLOR,
          opacity: statOpacity,
          marginTop: 8,
        }}
      >
        {subtext}
      </div>
    </div>
  );
};

export default SplitPanel;
