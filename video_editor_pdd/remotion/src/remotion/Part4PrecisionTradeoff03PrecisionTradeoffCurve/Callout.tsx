import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  FONT_FAMILY,
  CALLOUT_FONT_SIZE,
  CURVE_DATA,
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
} from "./constants";

function dataToPixel(
  dataX: number,
  dataY: number
): { px: number; py: number } {
  const px = CHART_LEFT + ((dataX - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
  const py =
    CHART_BOTTOM - ((dataY - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
  return { px, py };
}

function interpolateYFromData(dataX: number): number {
  if (dataX <= CURVE_DATA[0].x) return CURVE_DATA[0].y;
  if (dataX >= CURVE_DATA[CURVE_DATA.length - 1].x)
    return CURVE_DATA[CURVE_DATA.length - 1].y;
  for (let j = 0; j < CURVE_DATA.length - 1; j++) {
    if (dataX >= CURVE_DATA[j].x && dataX <= CURVE_DATA[j + 1].x) {
      const t =
        (dataX - CURVE_DATA[j].x) / (CURVE_DATA[j + 1].x - CURVE_DATA[j].x);
      return CURVE_DATA[j].y + t * (CURVE_DATA[j + 1].y - CURVE_DATA[j].y);
    }
  }
  return CURVE_DATA[CURVE_DATA.length - 1].y;
}

interface CalloutProps {
  /** X position in data space */
  dataX: number;
  /** Callout text (supports \n) */
  text: string;
  /** Accent color for text and line */
  color: string;
  /** Offset direction: "above-right" or "above-left" */
  anchor?: "above-right" | "above-left";
}

export const Callout: React.FC<CalloutProps> = ({
  dataX,
  text,
  color,
  anchor = "above-right",
}) => {
  const frame = useCurrentFrame();

  // Animate in with easeOut(back) scale 0.95→1.0 over 20 frames
  const appearProgress = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.back(1.5)),
  });

  const opacity = interpolate(frame, [0, 15], [0, 0.9], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const scale = 0.95 + 0.05 * appearProgress;

  const dataY = interpolateYFromData(dataX);
  const { px: curveX, py: curveY } = dataToPixel(dataX, dataY);

  // Position callout box above the curve point
  const offsetX = anchor === "above-right" ? 40 : -40;
  const offsetY = -80;
  const boxX = curveX + offsetX;
  const boxY = curveY + offsetY;

  const lines = text.split("\n");

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Connecting line from curve point to callout */}
        <line
          x1={curveX}
          y1={curveY}
          x2={boxX}
          y2={boxY + lines.length * 18}
          stroke={color}
          strokeWidth={1}
          opacity={0.3 * opacity}
        />
      </svg>

      {/* Callout text */}
      <div
        style={{
          position: "absolute",
          left: anchor === "above-right" ? boxX : boxX - 220,
          top: boxY,
          opacity,
          transform: `scale(${scale})`,
          transformOrigin:
            anchor === "above-right" ? "left bottom" : "right bottom",
        }}
      >
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: FONT_FAMILY,
              fontSize: CALLOUT_FONT_SIZE,
              fontWeight: 400,
              color,
              lineHeight: "20px",
              whiteSpace: "nowrap",
              textAlign: anchor === "above-right" ? "left" : "right",
            }}
          >
            {line}
          </div>
        ))}
      </div>
    </AbsoluteFill>
  );
};
