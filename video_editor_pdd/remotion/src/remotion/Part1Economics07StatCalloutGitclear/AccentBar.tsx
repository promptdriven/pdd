import React from "react";
import {
  ACCENT_BAR_WIDTH,
  CARD_HEIGHT,
  CARD_BORDER_RADIUS,
  ACCENT_RED,
  ACCENT_AMBER,
} from "./constants";

export const AccentBar: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: ACCENT_BAR_WIDTH,
        height: CARD_HEIGHT,
        background: `linear-gradient(to bottom, ${ACCENT_RED}, ${ACCENT_AMBER})`,
        borderTopLeftRadius: CARD_BORDER_RADIUS,
        borderBottomLeftRadius: CARD_BORDER_RADIUS,
      }}
    />
  );
};
