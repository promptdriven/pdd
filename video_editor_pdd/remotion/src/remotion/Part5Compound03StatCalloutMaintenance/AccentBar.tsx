import React from "react";
import { ACCENT_BAR_WIDTH, ACCENT_BAR_COLOR } from "./constants";

export const AccentBar: React.FC = () => {
  return (
    <div
      style={{
        width: ACCENT_BAR_WIDTH,
        height: "100%",
        backgroundColor: ACCENT_BAR_COLOR,
        flexShrink: 0,
      }}
    />
  );
};

export default AccentBar;
