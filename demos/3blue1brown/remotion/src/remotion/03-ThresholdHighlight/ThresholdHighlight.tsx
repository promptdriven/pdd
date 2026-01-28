import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { FrozenChart } from "./FrozenChart";
import { CrossingPointMarker } from "./CrossingPointMarker";
import { AnimatedLabel } from "./AnimatedLabel";
import {
  COLORS,
  CROSSING_POINT,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  BEATS,
  ThresholdHighlightPropsType,
} from "./constants";

export const ThresholdHighlight: React.FC<ThresholdHighlightPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Calculate crossing point position in pixels
  const getXPosition = (year: number) => {
    return (
      CHART_MARGINS.left +
      ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth
    );
  };

  const getYPosition = (hours: number) => {
    return (
      CHART_MARGINS.top +
      chartHeight -
      (hours / HOURS_RANGE.max) * chartHeight
    );
  };

  const crossingX = getXPosition(CROSSING_POINT.year);
  const crossingY = getYPosition(CROSSING_POINT.hours);

  // Title opacity (stays visible throughout)
  const titleOpacity = 1;

  // Narration text fade in during hold phase
  const narrationOpacity = interpolate(
    frame,
    [BEATS.HOLD_START, BEATS.HOLD_START + 30],
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

      {/* Frozen chart (both lines fully drawn) */}
      <FrozenChart />

      {/* Crossing point marker with pulse effects */}
      <CrossingPointMarker x={crossingX} y={crossingY} />

      {/* Animated label */}
      <AnimatedLabel
        text="The Threshold"
        targetX={crossingX}
        targetY={crossingY}
        offsetX={120}
        offsetY={-80}
      />

      {/* Legend (same as SockPriceChart) */}
      <div
        style={{
          position: "absolute",
          top: 120,
          right: 60,
          opacity: 1,
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

      {/* Narration text overlay - centered on screen */}
      {frame >= BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: narrationOpacity,
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
            "Darning made sense. You'd spend thirty minutes to save a dollar."
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
