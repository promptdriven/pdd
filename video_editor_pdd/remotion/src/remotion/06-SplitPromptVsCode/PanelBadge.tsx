import React from "react";

interface PanelBadgeProps {
  text: string;
  color: string;
  pillBg: string;
}

export const PanelBadge: React.FC<PanelBadgeProps> = ({ text, color, pillBg }) => {
  return (
    <div
      style={{
        display: "inline-block",
        fontFamily: "Inter, sans-serif",
        fontWeight: 600,
        fontSize: 14,
        color,
        backgroundColor: pillBg,
        padding: "4px 14px",
        borderRadius: 20,
        textTransform: "uppercase",
        letterSpacing: "0.1em",
        marginBottom: 12,
      }}
    >
      {text}
    </div>
  );
};

export default PanelBadge;
