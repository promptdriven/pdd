import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  LAYER_CARD_WIDTH,
  LAYER_CARD_HEIGHT,
  LAYER_CARD_RADIUS,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  ACCENT_BLUE,
  BORDER_GLOW,
  DIVIDER_COLOR,
} from "./constants";

interface LayerCardProps {
  title: string;
  subtitle: string;
  icon: string;
  bgColor: string;
  accentColor: string;
  revealFrame: number;
  cardIndex: number;
}

export const LayerCard: React.FC<LayerCardProps> = ({
  title,
  subtitle,
  icon,
  bgColor,
  accentColor,
  revealFrame,
  cardIndex,
}) => {
  const frame = useCurrentFrame();

  // Content fades in after the card is revealed
  const contentOpacity = interpolate(
    frame,
    [revealFrame, revealFrame + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Subtle breathing glow on the border
  const glowIntensity = interpolate(
    frame,
    [revealFrame + 20, revealFrame + 50, revealFrame + 80],
    [0.3, 0.7, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Pulse on the icon
  const iconScale = interpolate(
    frame,
    [revealFrame + 10, revealFrame + 25, revealFrame + 40],
    [0.6, 1.15, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  // Small data bar animation
  const barWidth = interpolate(
    frame,
    [revealFrame + 15, revealFrame + 45],
    [0, 100],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  return (
    <div
      style={{
        width: LAYER_CARD_WIDTH,
        height: LAYER_CARD_HEIGHT,
        borderRadius: LAYER_CARD_RADIUS,
        backgroundColor: bgColor,
        border: `2px solid ${accentColor}`,
        boxShadow: `0 0 ${20 * glowIntensity}px ${accentColor}40,
                     inset 0 1px 0 rgba(255,255,255,0.05)`,
        display: "flex",
        flexDirection: "column",
        padding: 32,
        position: "relative",
        overflow: "hidden",
      }}
    >
      {/* Corner accent */}
      <div
        style={{
          position: "absolute",
          top: 0,
          right: 0,
          width: 60,
          height: 60,
          background: `linear-gradient(135deg, ${accentColor}30 0%, transparent 60%)`,
          borderBottomLeftRadius: LAYER_CARD_RADIUS,
        }}
      />

      {/* Icon */}
      <div
        style={{
          opacity: contentOpacity,
          transform: `scale(${iconScale})`,
          fontSize: 36,
          fontFamily: "monospace",
          color: accentColor,
          marginBottom: 16,
          fontWeight: 700,
          width: 50,
          height: 50,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          backgroundColor: `${accentColor}15`,
          borderRadius: 12,
        }}
      >
        {icon}
      </div>

      {/* Title */}
      <div
        style={{
          opacity: contentOpacity,
          fontSize: 28,
          fontWeight: 700,
          color: TEXT_PRIMARY,
          fontFamily: "Inter, system-ui, sans-serif",
          marginBottom: 8,
          letterSpacing: "-0.02em",
        }}
      >
        {title}
      </div>

      {/* Divider */}
      <div
        style={{
          width: 64,
          height: 2,
          backgroundColor: DIVIDER_COLOR,
          opacity: contentOpacity * 0.85,
          marginBottom: 12,
          borderRadius: 1,
        }}
      />

      {/* Subtitle */}
      <div
        style={{
          opacity: Math.max(contentOpacity * 0.82, 0),
          fontSize: 18,
          color: TEXT_SECONDARY,
          fontFamily: "Inter, system-ui, sans-serif",
          fontWeight: 400,
          lineHeight: 1.4,
          marginBottom: 20,
        }}
      >
        {subtitle}
      </div>

      {/* Data bar visualization */}
      <div
        style={{
          opacity: contentOpacity,
          display: "flex",
          alignItems: "center",
          gap: 12,
          marginTop: "auto",
        }}
      >
        <div
          style={{
            flex: 1,
            height: 6,
            backgroundColor: "rgba(255,255,255,0.08)",
            borderRadius: 3,
            overflow: "hidden",
          }}
        >
          <div
            style={{
              width: `${barWidth}%`,
              height: "100%",
              backgroundColor: accentColor,
              borderRadius: 3,
              boxShadow: `0 0 8px ${accentColor}60`,
            }}
          />
        </div>
        <span
          style={{
            fontSize: 14,
            fontFamily: "monospace",
            color: accentColor,
            fontWeight: 600,
            minWidth: 40,
          }}
        >
          {Math.round(barWidth)}%
        </span>
      </div>
    </div>
  );
};

export default LayerCard;
