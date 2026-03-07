import React from "react";
import {
  BAR_X_START,
  BAR_WIDTH,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_Y,
  LEFT_POS,
  RIGHT_POS,
  FONT_FAMILY,
  WHITE,
} from "./constants";

interface ContextCardProps {
  title: string;
  traits: string;
  color: string;
  position: "left" | "right";
  opacity: number;
  scale: number;
  icon: "rocket" | "shield";
}

const RocketIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg
    width="80"
    height="80"
    viewBox="0 0 80 80"
    fill="none"
    style={{ position: "absolute", right: 16, bottom: 16, opacity: 0.2 }}
  >
    <path
      d="M40 8C40 8 20 24 20 48C20 56 24 64 32 68L36 56H44L48 68C56 64 60 56 60 48C60 24 40 8 40 8Z"
      fill={color}
    />
    <circle cx="40" cy="36" r="6" fill={color} opacity="0.5" />
    <path d="M28 52L16 60L24 48" fill={color} opacity="0.7" />
    <path d="M52 52L64 60L56 48" fill={color} opacity="0.7" />
  </svg>
);

const ShieldIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg
    width="80"
    height="80"
    viewBox="0 0 80 80"
    fill="none"
    style={{ position: "absolute", right: 16, bottom: 16, opacity: 0.2 }}
  >
    <path
      d="M40 8L12 24V44C12 60 24 72 40 76C56 72 68 60 68 44V24L40 8Z"
      fill={color}
    />
    <rect x="34" y="32" width="12" height="16" rx="2" fill={color} opacity="0.5" />
    <circle cx="40" cy="30" r="8" stroke={color} strokeWidth="3" fill="none" opacity="0.5" />
    <circle cx="40" cy="44" r="2" fill={color} opacity="0.8" />
  </svg>
);

export const ContextCard: React.FC<ContextCardProps> = ({
  title,
  traits,
  color,
  position,
  opacity,
  scale,
  icon,
}) => {
  const normalizedPos = position === "left" ? LEFT_POS : RIGHT_POS;
  const cardCenterX = BAR_X_START + normalizedPos * BAR_WIDTH;
  const cardLeft = cardCenterX - CARD_WIDTH / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: cardLeft,
        top: CARD_Y,
        width: CARD_WIDTH,
        height: CARD_HEIGHT,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: "top center",
        background: `${color}1F`,
        backdropFilter: "blur(8px)",
        WebkitBackdropFilter: "blur(8px)",
        border: `1px solid ${color}4D`,
        borderRadius: 16,
        padding: 28,
        overflow: "hidden",
      }}
    >
      {/* Icon */}
      {icon === "rocket" ? (
        <RocketIcon color={color} />
      ) : (
        <ShieldIcon color={color} />
      )}

      {/* Title */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: 24,
          color: WHITE,
          marginBottom: 16,
          position: "relative",
          zIndex: 1,
        }}
      >
        {title}
      </div>

      {/* Traits */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontWeight: 400,
          fontSize: 16,
          color: `${color}CC`,
          lineHeight: 1.6,
          position: "relative",
          zIndex: 1,
        }}
      >
        {traits}
      </div>
    </div>
  );
};
