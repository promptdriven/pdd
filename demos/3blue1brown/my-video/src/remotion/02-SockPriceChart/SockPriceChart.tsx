import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import {
  COLORS,
  CHART_DATA,
  BEATS,
  SockPriceChartPropsType,
} from "./constants";

export const SockPriceChart: React.FC<SockPriceChartPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();

  // Title fade in
  const titleOpacity = interpolate(
    frame,
    [BEATS.AXES_FADE_IN_START, BEATS.AXES_FADE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Title */}
      {showTitle && (
        <div
          style={{
            position: "absolute",
            top: 30,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 42,
            fontWeight: 700,
            color: COLORS.TITLE,
            opacity: titleOpacity,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          }}
        >
          The Economics of Sock Repair
        </div>
      )}

      {/* Chart axes and grid */}
      <ChartAxes />

      {/* Cost to Buy line */}
      <AnimatedLine
        data={CHART_DATA.costToBuy}
        color={COLORS.LINE_BUY}
        startFrame={BEATS.BUY_LINE_START}
        endFrame={BEATS.BUY_LINE_END}
        label="Cost to Buy"
      />

      {/* Cost to Repair line */}
      <AnimatedLine
        data={CHART_DATA.costToRepair}
        color={COLORS.LINE_REPAIR}
        startFrame={BEATS.REPAIR_LINE_START}
        endFrame={BEATS.REPAIR_LINE_END}
        strokeWidth={4}
        label="Cost to Repair"
      />

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 120,
          right: 60,
          opacity: interpolate(
            frame,
            [BEATS.REPAIR_LINE_END, BEATS.REPAIR_LINE_END + 30],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
        }}
      >
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 16,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 24,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 40,
              height: 5,
              backgroundColor: COLORS.LINE_BUY,
              marginRight: 16,
              borderRadius: 2,
            }}
          />
          Cost to Buy
        </div>
        <div
          style={{
            display: "flex",
            alignItems: "center",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 24,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 40,
              height: 5,
              backgroundColor: COLORS.LINE_REPAIR,
              marginRight: 16,
              borderRadius: 2,
            }}
          />
          Cost to Repair
        </div>
      </div>

      {/* Narration text overlay (appears at hold phase) - centered on screen */}
      {frame >= BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: interpolate(
              frame,
              [BEATS.HOLD_START, BEATS.HOLD_START + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.7)",
            padding: "30px 50px",
            borderRadius: 12,
          }}
        >
          <p
            style={{
              fontFamily: "Georgia, serif",
              fontSize: 36,
              color: "#ffffff",
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              fontStyle: "italic",
              maxWidth: 900,
              lineHeight: 1.5,
              margin: 0,
            }}
          >
            "This isn't nostalgia. It's economics."
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
