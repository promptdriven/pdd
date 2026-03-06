import React from "react";
import { useCurrentFrame, interpolate, spring, Easing } from "remotion";
import {
  BOX_WIDTH,
  BOX_HEIGHT,
  BOX_BORDER_WIDTH,
  BOX_BORDER_RADIUS,
  ICON_SIZE,
  FPS,
  SPRING_DAMPING,
  SPRING_STIFFNESS,
  GLOW_PULSE_SPEED,
  GLOW_PULSE_MIN,
  GLOW_PULSE_MAX,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

type IconType = "document" | "code" | "shield";

interface TriadBoxProps {
  centerX: number;
  centerY: number;
  borderColor: string;
  fill: string;
  iconColor: string;
  glowColor: string;
  label: string;
  subtitle: string;
  icon: IconType;
  entryFrame: number;
  pulseHighlightFrame: number;
}

/** Renders the SVG icon for each box type */
const BoxIcon: React.FC<{ icon: IconType; color: string; size: number }> = ({
  icon,
  color,
  size,
}) => {
  const half = size / 2;

  if (icon === "document") {
    // Document / scroll silhouette
    const w = size * 0.65;
    const h = size * 0.85;
    const foldSize = size * 0.18;
    return (
      <g>
        <path
          d={`M ${-w / 2} ${-h / 2}
              L ${w / 2 - foldSize} ${-h / 2}
              L ${w / 2} ${-h / 2 + foldSize}
              L ${w / 2} ${h / 2}
              L ${-w / 2} ${h / 2} Z`}
          fill="none"
          stroke={color}
          strokeWidth={2.5}
          strokeLinejoin="round"
        />
        <path
          d={`M ${w / 2 - foldSize} ${-h / 2}
              L ${w / 2 - foldSize} ${-h / 2 + foldSize}
              L ${w / 2} ${-h / 2 + foldSize}`}
          fill="none"
          stroke={color}
          strokeWidth={2}
          opacity={0.7}
        />
        {/* Text lines */}
        <line
          x1={-w / 2 + 8}
          y1={-h / 2 + foldSize + 10}
          x2={w / 2 - 8}
          y2={-h / 2 + foldSize + 10}
          stroke={color}
          strokeWidth={2}
          opacity={0.5}
        />
        <line
          x1={-w / 2 + 8}
          y1={-h / 2 + foldSize + 22}
          x2={w / 2 - 14}
          y2={-h / 2 + foldSize + 22}
          stroke={color}
          strokeWidth={2}
          opacity={0.4}
        />
        <line
          x1={-w / 2 + 8}
          y1={-h / 2 + foldSize + 34}
          x2={w / 2 - 8}
          y2={-h / 2 + foldSize + 34}
          stroke={color}
          strokeWidth={2}
          opacity={0.3}
        />
      </g>
    );
  }

  if (icon === "code") {
    // Code brackets </>
    const bW = half * 0.5;
    const bH = half * 0.7;
    return (
      <g>
        {/* Left bracket < */}
        <polyline
          points={`${-bW},${-bH} ${-bW - 12},0 ${-bW},${bH}`}
          fill="none"
          stroke={color}
          strokeWidth={3}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
        {/* Right bracket > */}
        <polyline
          points={`${bW},${-bH} ${bW + 12},0 ${bW},${bH}`}
          fill="none"
          stroke={color}
          strokeWidth={3}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
        {/* Slash / */}
        <line
          x1={6}
          y1={-bH + 2}
          x2={-6}
          y2={bH - 2}
          stroke={color}
          strokeWidth={2.5}
          strokeLinecap="round"
        />
      </g>
    );
  }

  // shield — shield with checkmark
  const shW = half * 0.72;
  const shH = half * 0.9;
  return (
    <g>
      <path
        d={`M 0 ${-shH}
            C ${shW * 0.4} ${-shH} ${shW} ${-shH * 0.7} ${shW} ${-shH * 0.3}
            L ${shW} ${shH * 0.2}
            C ${shW} ${shH * 0.7} 0 ${shH} 0 ${shH}
            C 0 ${shH} ${-shW} ${shH * 0.7} ${-shW} ${shH * 0.2}
            L ${-shW} ${-shH * 0.3}
            C ${-shW} ${-shH * 0.7} ${-shW * 0.4} ${-shH} 0 ${-shH} Z`}
        fill="none"
        stroke={color}
        strokeWidth={2.5}
        strokeLinejoin="round"
      />
      {/* Checkmark */}
      <polyline
        points={`${-shW * 0.35},${shH * 0.05} ${-shW * 0.05},${shH * 0.35} ${shW * 0.4},${-shH * 0.25}`}
        fill="none"
        stroke={color}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </g>
  );
};

export const TriadBox: React.FC<TriadBoxProps> = ({
  centerX,
  centerY,
  borderColor,
  fill,
  iconColor,
  glowColor,
  label,
  subtitle,
  icon,
  entryFrame,
  pulseHighlightFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - entryFrame;

  if (localFrame < 0) return null;

  // Spring scale-in
  const scale = spring({
    frame: localFrame,
    fps: FPS,
    config: { damping: SPRING_DAMPING, stiffness: SPRING_STIFFNESS },
  });

  // Content fade-in (icon, label, subtitle appear as box scales in)
  const contentOpacity = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Glow pulse (sinusoidal)
  const glowOpacity = interpolate(
    Math.sin(frame * GLOW_PULSE_SPEED),
    [-1, 1],
    [GLOW_PULSE_MIN, GLOW_PULSE_MAX]
  );

  // Pulse brightness on synthesis highlight
  const pulseLocalFrame = frame - pulseHighlightFrame;
  let brightness = 1.0;
  if (pulseLocalFrame >= 0 && pulseLocalFrame <= 30) {
    brightness = interpolate(
      pulseLocalFrame,
      [0, 15, 30],
      [1.0, 1.4, 1.0],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.sin),
      }
    );
  }

  // Master fade-out
  const fadeOut = interpolate(frame, [FADEOUT_START, FADEOUT_END], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.cubic),
  });

  const left = centerX - BOX_WIDTH / 2;
  const top = centerY - BOX_HEIGHT / 2;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: BOX_WIDTH,
        height: BOX_HEIGHT,
        transform: `scale(${scale})`,
        transformOrigin: "center center",
        opacity: fadeOut,
        filter: `brightness(${brightness})`,
      }}
    >
      {/* Box container */}
      <div
        style={{
          width: "100%",
          height: "100%",
          borderRadius: BOX_BORDER_RADIUS,
          border: `${BOX_BORDER_WIDTH}px solid ${borderColor}`,
          background: fill,
          boxShadow: `0 0 20px ${glowColor}`,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          gap: 8,
          opacity: glowOpacity > 0 ? 1 : 1,
          // Apply pulsing glow via boxShadow
          ...(glowOpacity > 0
            ? {
                boxShadow: `0 0 ${20 * (glowOpacity / GLOW_PULSE_MAX)}px ${glowColor}`,
              }
            : {}),
        }}
      >
        {/* Icon */}
        <svg
          width={ICON_SIZE}
          height={ICON_SIZE}
          viewBox={`${-ICON_SIZE / 2} ${-ICON_SIZE / 2} ${ICON_SIZE} ${ICON_SIZE}`}
          style={{ opacity: contentOpacity, marginTop: 16 }}
        >
          <BoxIcon icon={icon} color={iconColor} size={ICON_SIZE} />
        </svg>

        {/* Label */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: 24,
            color: borderColor,
            letterSpacing: "0.1em",
            textAlign: "center",
            opacity: contentOpacity,
          }}
        >
          {label}
        </div>

        {/* Subtitle */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontStyle: "italic",
            fontSize: 18,
            color: borderColor,
            opacity: contentOpacity * 0.7,
            textAlign: "center",
          }}
        >
          {subtitle}
        </div>
      </div>
    </div>
  );
};
