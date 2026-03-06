import React from "react";
import { DETAIL_SIZE, DETAIL_ICON_SIZE } from "./constants";
import { WarningIcon } from "./WarningIcon";
import { TrendingUpIcon } from "./TrendingUpIcon";

interface DetailRowProps {
  text: string;
  color: string;
  icon: "warning" | "trending_up";
  opacity: number;
  translateX: number;
}

export const DetailRow: React.FC<DetailRowProps> = ({
  text,
  color,
  icon,
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
      {icon === "warning" ? (
        <WarningIcon size={DETAIL_ICON_SIZE} color={color} />
      ) : (
        <TrendingUpIcon size={DETAIL_ICON_SIZE} color={color} />
      )}
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
