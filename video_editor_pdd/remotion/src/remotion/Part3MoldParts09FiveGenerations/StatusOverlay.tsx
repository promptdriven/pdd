import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  PANEL_W,
  PANEL_H,
  STATUS_ICON_SIZE,
  STATUS_RED,
  STATUS_YELLOW,
  STATUS_GREEN,
  RED_X_FRAME,
  YELLOW_WARN_FRAME,
  GREEN_CHECK_FRAME,
} from "./constants";

// ── Red X icon ──────────────────────────────────────────────────────────────
const RedX: React.FC<{ progress: number; shake: number }> = ({ progress, shake }) => (
  <div
    style={{
      position: "absolute",
      inset: 0,
      display: "flex",
      alignItems: "center",
      justifyContent: "center",
      backgroundColor: `rgba(239, 68, 68, 0.08)`,
      borderRadius: 8,
      opacity: progress,
      transform: `translateX(${shake}px) scale(${interpolate(progress, [0, 1], [1.4, 1])})`,
    }}
  >
    <svg
      width={STATUS_ICON_SIZE}
      height={STATUS_ICON_SIZE}
      viewBox="0 0 48 48"
    >
      <circle cx="24" cy="24" r="22" fill="rgba(239,68,68,0.15)" />
      <line x1="14" y1="14" x2="34" y2="34" stroke={STATUS_RED} strokeWidth="4" strokeLinecap="round" />
      <line x1="34" y1="14" x2="14" y2="34" stroke={STATUS_RED} strokeWidth="4" strokeLinecap="round" />
    </svg>
  </div>
);

// ── Yellow Warning ──────────────────────────────────────────────────────────
const YellowWarning: React.FC<{ progress: number; wobble: number }> = ({ progress, wobble }) => (
  <div
    style={{
      position: "absolute",
      inset: 0,
      display: "flex",
      alignItems: "center",
      justifyContent: "center",
      backgroundColor: `rgba(251, 191, 36, 0.06)`,
      borderRadius: 8,
      opacity: progress,
      transform: `rotate(${wobble}deg) scale(${interpolate(progress, [0, 1], [1.3, 1])})`,
    }}
  >
    <svg
      width={STATUS_ICON_SIZE}
      height={STATUS_ICON_SIZE}
      viewBox="0 0 48 48"
    >
      <path
        d="M24 4 L44 42 L4 42 Z"
        fill="rgba(251,191,36,0.15)"
        stroke={STATUS_YELLOW}
        strokeWidth="2.5"
        strokeLinejoin="round"
      />
      <line x1="24" y1="18" x2="24" y2="30" stroke={STATUS_YELLOW} strokeWidth="3" strokeLinecap="round" />
      <circle cx="24" cy="36" r="2" fill={STATUS_YELLOW} />
    </svg>
  </div>
);

// ── Green Checkmark ─────────────────────────────────────────────────────────
const GreenCheck: React.FC<{ progress: number; burstRadius: number }> = ({ progress, burstRadius }) => (
  <div
    style={{
      position: "absolute",
      inset: 0,
      display: "flex",
      alignItems: "center",
      justifyContent: "center",
      borderRadius: 8,
      opacity: progress,
      transform: `scale(${interpolate(progress, [0, 1], [0.5, 1])})`,
    }}
  >
    {/* Radial glow burst */}
    <div
      style={{
        position: "absolute",
        width: burstRadius * 2,
        height: burstRadius * 2,
        borderRadius: "50%",
        background: `radial-gradient(circle, rgba(74,222,128,0.25) 0%, transparent 70%)`,
      }}
    />
    <svg
      width={STATUS_ICON_SIZE}
      height={STATUS_ICON_SIZE}
      viewBox="0 0 48 48"
    >
      <circle cx="24" cy="24" r="22" fill="rgba(74,222,128,0.15)" />
      <polyline
        points="14,24 22,33 36,16"
        fill="none"
        stroke={STATUS_GREEN}
        strokeWidth="4"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  </div>
);

// ── Status overlay per-panel ────────────────────────────────────────────────
interface StatusOverlayProps {
  panelIndex: number;
  status: "fail" | "partial" | "pass";
  x: number;
  y: number;
}

export const StatusOverlay: React.FC<StatusOverlayProps> = ({
  panelIndex,
  status,
  x,
  y,
}) => {
  const frame = useCurrentFrame();

  if (status === "fail") {
    const startFrame = RED_X_FRAME + (panelIndex === 1 ? 5 : 0); // slight stagger between panels 1 & 2
    const localFrame = frame - startFrame;
    if (localFrame < 0) return null;

    const progress = interpolate(localFrame, [0, 10], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.7)),
    });

    // Shake: quick lateral oscillation
    const shakeAmount =
      localFrame < 10
        ? 3 * Math.sin(localFrame * 3) * (1 - localFrame / 10)
        : 0;

    return (
      <div style={{ position: "absolute", left: x, top: y, width: PANEL_W, height: PANEL_H, pointerEvents: "none" }}>
        <RedX progress={progress} shake={shakeAmount} />
      </div>
    );
  }

  if (status === "partial") {
    const stagger = panelIndex === 3 ? 5 : 0;
    const startFrame = YELLOW_WARN_FRAME + stagger;
    const localFrame = frame - startFrame;
    if (localFrame < 0) return null;

    const progress = interpolate(localFrame, [0, 12], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.elastic(1)),
    });

    // Wobble
    const wobble =
      localFrame < 18
        ? 6 * Math.sin(localFrame * 1.5) * Math.exp(-localFrame * 0.12)
        : 0;

    return (
      <div style={{ position: "absolute", left: x, top: y, width: PANEL_W, height: PANEL_H, pointerEvents: "none" }}>
        <YellowWarning progress={progress} wobble={wobble} />
      </div>
    );
  }

  if (status === "pass") {
    const localFrame = frame - GREEN_CHECK_FRAME;
    if (localFrame < 0) return null;

    const progress = interpolate(localFrame, [0, 15], [0, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.exp),
    });

    // Burst expands then settles
    const burstRadius = interpolate(localFrame, [0, 15, 40], [10, 80, 50], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });

    return (
      <div style={{ position: "absolute", left: x, top: y, width: PANEL_W, height: PANEL_H, pointerEvents: "none" }}>
        <GreenCheck progress={progress} burstRadius={burstRadius} />
      </div>
    );
  }

  return null;
};
