import React from "react";
import { useCurrentFrame, useVideoConfig, spring, interpolate, Easing } from "remotion";
import {
  BOX_W,
  BOX_H,
  BOX_RADIUS,
  BOX_BORDER_WIDTH,
  ICON_SIZE,
  FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_LETTER_SPACING,
  SUBTITLE_FONT_SIZE,
  GLOW_ANGULAR_VELOCITY,
} from "./constants";

interface TriadBoxProps {
  centerX: number;
  centerY: number;
  label: string;
  subtitle: string;
  borderColor: string;
  fillColor: string;
  iconColor: string;
  glowColor: string;
  icon: "document" | "code" | "shield";
  enterFrame: number;
  pulseHighlightFrame: number | null;
}

const DocumentIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <rect x="14" y="6" width="36" height="48" rx="4" stroke={color} strokeWidth="3" fill="none" />
    <path d="M38 6V18H50" stroke={color} strokeWidth="3" fill="none" strokeLinejoin="round" />
    <line x1="22" y1="28" x2="42" y2="28" stroke={color} strokeWidth="2" />
    <line x1="22" y1="36" x2="42" y2="36" stroke={color} strokeWidth="2" />
    <line x1="22" y1="44" x2="34" y2="44" stroke={color} strokeWidth="2" />
  </svg>
);

const CodeIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <path d="M22 18L8 32L22 46" stroke={color} strokeWidth="3" strokeLinecap="round" strokeLinejoin="round" />
    <path d="M42 18L56 32L42 46" stroke={color} strokeWidth="3" strokeLinecap="round" strokeLinejoin="round" />
    <line x1="36" y1="14" x2="28" y2="50" stroke={color} strokeWidth="2.5" strokeLinecap="round" />
  </svg>
);

const ShieldIcon: React.FC<{ color: string; size: number }> = ({
  color,
  size,
}) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <path
      d="M32 6L10 18V34C10 46 20 56 32 58C44 56 54 46 54 34V18L32 6Z"
      stroke={color}
      strokeWidth="3"
      fill="none"
      strokeLinejoin="round"
    />
    <path
      d="M22 32L28 40L42 24"
      stroke={color}
      strokeWidth="3"
      strokeLinecap="round"
      strokeLinejoin="round"
    />
  </svg>
);

export const TriadBox: React.FC<TriadBoxProps> = ({
  centerX,
  centerY,
  label,
  subtitle,
  borderColor,
  fillColor,
  iconColor,
  glowColor,
  icon,
  enterFrame,
  pulseHighlightFrame,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const localFrame = frame - enterFrame;

  if (localFrame < 0) return null;

  // Spring scale-in per spec: damping 14, stiffness 180
  const scaleRaw = spring({
    frame: localFrame,
    fps,
    config: { damping: 14, stiffness: 180, mass: 1 },
  });

  // Content fade-in (icon, label, subtitle)
  const contentOpacity = interpolate(localFrame, [5, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Glow pulse: sinusoidal, 2.5s period
  const glowIntensity = interpolate(
    Math.sin(frame * GLOW_ANGULAR_VELOCITY),
    [-1, 1],
    [0.15, 0.3]
  );

  // Pulse on synthesis highlight: brightness 1.0 → 1.4 → 1.0 over 30 frames
  let brightnessMultiplier = 1;
  if (pulseHighlightFrame !== null) {
    const pulseLocal = frame - pulseHighlightFrame;
    if (pulseLocal >= 0 && pulseLocal <= 30) {
      brightnessMultiplier = interpolate(
        pulseLocal,
        [0, 15, 30],
        [1.0, 1.4, 1.0],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.inOut(Easing.sin),
        }
      );
    }
  }

  const glowRadius = 20 * glowIntensity * brightnessMultiplier;
  const left = centerX - BOX_W / 2;
  const top = centerY - BOX_H / 2;

  const IconComponent =
    icon === "document"
      ? DocumentIcon
      : icon === "code"
        ? CodeIcon
        : ShieldIcon;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: BOX_W,
        height: BOX_H,
        borderRadius: BOX_RADIUS,
        border: `${BOX_BORDER_WIDTH}px solid ${borderColor}`,
        backgroundColor: fillColor,
        boxShadow: `0 0 ${glowRadius}px ${glowColor}`,
        transform: `scale(${scaleRaw})`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        gap: 8,
        filter: brightnessMultiplier > 1 ? `brightness(${brightnessMultiplier})` : undefined,
      }}
    >
      {/* Icon */}
      <div style={{ opacity: contentOpacity }}>
        <IconComponent color={iconColor} size={ICON_SIZE} />
      </div>

      {/* Label */}
      <div
        style={{
          opacity: contentOpacity,
          fontFamily: FONT_FAMILY,
          fontSize: LABEL_FONT_SIZE,
          fontWeight: 900,
          color: borderColor,
          letterSpacing: LABEL_LETTER_SPACING,
          textAlign: "center",
        }}
      >
        {label}
      </div>

      {/* Subtitle */}
      <div
        style={{
          opacity: contentOpacity * 0.7,
          fontFamily: FONT_FAMILY,
          fontSize: SUBTITLE_FONT_SIZE,
          fontWeight: 500,
          fontStyle: "italic",
          color: borderColor,
          textAlign: "center",
        }}
      >
        {subtitle}
      </div>
    </div>
  );
};
