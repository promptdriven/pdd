import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PANEL_RADIUS,
  PANEL_BG,
  FONT_FAMILY,
  FADEOUT_START,
  FADEOUT_END,
  OUTCOME_FADE_START,
  OUTCOME_FADE_END,
} from "./constants";

interface SplitPanelProps {
  x: number;
  y: number;
  w: number;
  h: number;
  tintBg: string;
  accentColor: string;
  header: string;
  icon: React.ReactNode;
  costCurve: React.ReactNode;
  outcome: string;
  translateX: number;
  opacity: number;
  headerFadeStart: number;
  headerFadeEnd: number;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({
  x,
  y,
  w,
  h,
  tintBg,
  accentColor,
  header,
  icon,
  costCurve,
  outcome,
  translateX,
  opacity,
  headerFadeStart,
  headerFadeEnd,
}) => {
  const frame = useCurrentFrame();

  const headerOpacity = interpolate(
    frame,
    [headerFadeStart, headerFadeEnd, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    },
  );

  const outcomeOpacity = interpolate(
    frame,
    [OUTCOME_FADE_START, OUTCOME_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // easeOutBack approximation for scale
  const outcomeScale = interpolate(
    frame,
    [OUTCOME_FADE_START, OUTCOME_FADE_END],
    [0.7, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: (t: number) => {
        const c1 = 1.70158;
        const c3 = c1 + 1;
        return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
      },
    },
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
        gap: 20,
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
          fontFamily: FONT_FAMILY,
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

      {/* Cost curve */}
      <div style={{ position: "relative", zIndex: 1 }}>
        {costCurve}
      </div>

      {/* Outcome word */}
      <div
        style={{
          position: "relative",
          zIndex: 1,
          fontFamily: FONT_FAMILY,
          fontWeight: 900,
          fontSize: 48,
          color: accentColor,
          textTransform: "uppercase",
          opacity: outcomeOpacity,
          transform: `scale(${outcomeScale})`,
          textShadow: `0 4px 24px ${accentColor}40`,
          marginTop: 8,
        }}
      >
        {outcome}
      </div>
    </div>
  );
};

export default SplitPanel;
