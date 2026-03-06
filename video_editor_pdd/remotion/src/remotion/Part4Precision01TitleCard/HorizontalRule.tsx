import React from "react";
import { AMBER, RULE_Y } from "./constants";

export const HorizontalRule: React.FC<{ width: number; opacity: number }> = ({
  width,
  opacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        top: RULE_Y,
        left: "50%",
        transform: "translateX(-50%)",
        width,
        height: 2,
        backgroundColor: AMBER,
        opacity: opacity * 0.6,
      }}
    />
  );
};
