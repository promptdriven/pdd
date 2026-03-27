// StatusOverlay.tsx — Red X, Yellow Warning, Green Checkmark overlays
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { STATUS_ICON_SIZE, FAIL_COLOR, WARN_COLOR, PASS_COLOR } from "./constants";

// ─── Red X Icon ───────────────────────────────────────────────────────
export const RedXIcon: React.FC<{ size: number }> = ({ size }) => (
  <svg width={size} height={size} viewBox="0 0 48 48">
    <circle cx="24" cy="24" r="22" fill={FAIL_COLOR} opacity={0.15} />
    <line
      x1="14"
      y1="14"
      x2="34"
      y2="34"
      stroke={FAIL_COLOR}
      strokeWidth="4"
      strokeLinecap="round"
    />
    <line
      x1="34"
      y1="14"
      x2="14"
      y2="34"
      stroke={FAIL_COLOR}
      strokeWidth="4"
      strokeLinecap="round"
    />
  </svg>
);

// ─── Yellow Warning Triangle ──────────────────────────────────────────
export const WarnIcon: React.FC<{ size: number }> = ({ size }) => (
  <svg width={size} height={size} viewBox="0 0 48 48">
    <polygon
      points="24,6 44,42 4,42"
      fill="none"
      stroke={WARN_COLOR}
      strokeWidth="3"
      strokeLinejoin="round"
    />
    <line
      x1="24"
      y1="20"
      x2="24"
      y2="30"
      stroke={WARN_COLOR}
      strokeWidth="3"
      strokeLinecap="round"
    />
    <circle cx="24" cy="36" r="2" fill={WARN_COLOR} />
  </svg>
);

// ─── Green Checkmark ──────────────────────────────────────────────────
export const CheckIcon: React.FC<{ size: number }> = ({ size }) => (
  <svg width={size} height={size} viewBox="0 0 48 48">
    <circle cx="24" cy="24" r="22" fill={PASS_COLOR} opacity={0.15} />
    <polyline
      points="14,24 22,32 34,16"
      fill="none"
      stroke={PASS_COLOR}
      strokeWidth="4"
      strokeLinecap="round"
      strokeLinejoin="round"
    />
  </svg>
);

// ─── Status Overlay Container ─────────────────────────────────────────
interface StatusOverlayProps {
  type: "x" | "warning" | "check";
  /** Frame offset relative to the Sequence this is placed in */
  animationDuration: number;
}

export const StatusOverlay: React.FC<StatusOverlayProps> = ({
  type,
  animationDuration,
}) => {
  const frame = useCurrentFrame();
  const size = STATUS_ICON_SIZE;

  // Scale-in with overshoot for stamps
  const scaleIn = interpolate(frame, [0, animationDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.back(1.7)),
  });

  // Shake for X marks (3px horizontal shake over first 10 frames)
  let shakeX = 0;
  if (type === "x" && frame < 10) {
    shakeX = Math.sin(frame * 4) * 3 * (1 - frame / 10);
  }

  // Wobble for warnings (rotation oscillation)
  let wobbleRotation = 0;
  if (type === "warning" && frame < 12) {
    wobbleRotation = Math.sin(frame * 3) * 8 * (1 - frame / 12);
  }

  // Glow burst for checkmark
  const glowOpacity =
    type === "check"
      ? interpolate(frame, [0, 15, 40], [0, 0.6, 0.3], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        pointerEvents: "none",
      }}
    >
      {/* Glow burst background for check */}
      {type === "check" && (
        <div
          style={{
            position: "absolute",
            width: 120,
            height: 120,
            borderRadius: "50%",
            background: `radial-gradient(circle, ${PASS_COLOR}60 0%, transparent 70%)`,
            opacity: glowOpacity,
          }}
        />
      )}

      <div
        style={{
          transform: `scale(${scaleIn}) translateX(${shakeX}px) rotate(${wobbleRotation}deg)`,
        }}
      >
        {type === "x" && <RedXIcon size={size} />}
        {type === "warning" && <WarnIcon size={size} />}
        {type === "check" && <CheckIcon size={size} />}
      </div>
    </div>
  );
};
