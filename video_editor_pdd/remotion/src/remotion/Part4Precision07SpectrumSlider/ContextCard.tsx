import React from "react";
import {
  BAR_X,
  BAR_WIDTH,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_Y,
  CARD_RADIUS,
  FONT_FAMILY,
  CARD_TITLE_SIZE,
  CARD_TRAITS_SIZE,
} from "./constants";

interface ContextCardProps {
  title: string;
  traits: string;
  color: string;
  bgColor: string;
  borderColor: string;
  /** Normalized position 0-1 along the bar */
  position: number;
  opacity: number;
  scale: number;
  /** SVG icon path data */
  iconPath: string;
}

export const ContextCard: React.FC<ContextCardProps> = ({
  title,
  traits,
  color,
  bgColor,
  borderColor,
  position,
  opacity,
  scale,
  iconPath,
}) => {
  const cx = BAR_X + position * BAR_WIDTH;
  const cardLeft = cx - CARD_WIDTH / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: cardLeft,
        top: CARD_Y,
        width: CARD_WIDTH,
        height: CARD_HEIGHT,
        borderRadius: CARD_RADIUS,
        backgroundColor: bgColor,
        backdropFilter: "blur(8px)",
        WebkitBackdropFilter: "blur(8px)",
        border: `1px solid ${borderColor}`,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: "center top",
        display: "flex",
        flexDirection: "column",
        justifyContent: "center",
        alignItems: "center",
        padding: 28,
        boxSizing: "border-box",
        overflow: "hidden",
      }}
    >
      {/* Background icon watermark */}
      <svg
        width={80}
        height={80}
        viewBox="0 0 24 24"
        style={{
          position: "absolute",
          right: 20,
          top: 20,
          opacity: 0.2,
        }}
      >
        <path d={iconPath} fill={color} />
      </svg>

      {/* Connecting line from bar to card */}
      <div
        style={{
          position: "absolute",
          left: CARD_WIDTH / 2 - 1,
          top: -20,
          width: 2,
          height: 20,
          background: `linear-gradient(to bottom, ${color}80, ${color}20)`,
        }}
      />

      {/* Title */}
      <div
        style={{
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: CARD_TITLE_SIZE,
          color: "#FFFFFF",
          textAlign: "center",
          marginBottom: 16,
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
          fontSize: CARD_TRAITS_SIZE,
          color: color,
          opacity: 0.8,
          textAlign: "center",
          lineHeight: 1.6,
          zIndex: 1,
        }}
      >
        {traits}
      </div>
    </div>
  );
};
