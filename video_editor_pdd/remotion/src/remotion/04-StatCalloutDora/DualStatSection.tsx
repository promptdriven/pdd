import React from "react";
import { ArrowIcon } from "./ArrowIcon";
import {
  LABEL_COLOR,
  LABEL_FONT_SIZE,
  RESULT_FONT_SIZE,
  ARROW_SIZE,
} from "./constants";

interface DualStatSectionProps {
  label: string;
  arrow: "up" | "down";
  arrowColor: string;
  result: string;
  resultColor: string;
  opacity: number;
  scale?: number;
  brightness?: number;
}

export const DualStatSection: React.FC<DualStatSectionProps> = ({
  label,
  arrow,
  arrowColor,
  result,
  resultColor,
  opacity,
  scale = 1,
  brightness = 1,
}) => {
  return (
    <div
      style={{
        opacity,
        display: "flex",
        flexDirection: "column",
        gap: 8,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 400,
          fontSize: LABEL_FONT_SIZE,
          color: LABEL_COLOR,
          lineHeight: 1.4,
        }}
      >
        {label}
      </div>

      {/* Arrow + Result */}
      <div
        style={{
          display: "flex",
          alignItems: "center",
          transform: `scale(${scale})`,
          transformOrigin: "left center",
          filter: `brightness(${brightness})`,
        }}
      >
        <ArrowIcon direction={arrow} color={arrowColor} size={ARROW_SIZE} />
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            fontSize: RESULT_FONT_SIZE,
            color: resultColor,
            lineHeight: 1.2,
          }}
        >
          {result}
        </div>
      </div>
    </div>
  );
};

export default DualStatSection;
