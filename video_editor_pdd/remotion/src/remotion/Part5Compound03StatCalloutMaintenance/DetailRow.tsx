import React from "react";
import { DETAIL_SIZE, DETAIL_ICON_SIZE } from "./constants";

interface DetailRowProps {
  text: string;
  color: string;
  opacity: number;
  translateX: number;
}

export const DetailRow: React.FC<DetailRowProps> = ({
  text,
  color,
  opacity,
  translateX,
}) => {
  return (
    <div
      style={{
        display: "flex",
        alignItems: "center",
        gap: 10,
        opacity,
        transform: `translateX(${translateX}px)`,
        marginTop: 8,
      }}
    >
      {/* Dash icon */}
      <div
        style={{
          width: DETAIL_ICON_SIZE,
          height: 2,
          backgroundColor: color,
          flexShrink: 0,
        }}
      />
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 600,
          fontSize: DETAIL_SIZE,
          color,
          lineHeight: 1.3,
        }}
      >
        {text}
      </div>
    </div>
  );
};

export default DetailRow;
