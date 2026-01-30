import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { CodeCostChart } from "./CodeCostChart";
import { WeAreHereMarker } from "./WeAreHereMarker";
import { AnimatedArrow } from "./AnimatedArrow";
import {
  COLORS,
  CROSSING_POINT,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  BEATS,
  CrossingPointPropsType,
} from "./constants";
import { Easing } from "remotion";

export const CrossingPoint: React.FC<CrossingPointPropsType> = ({
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

  // Label position (below and right of crossing point)
  const labelOffsetX = 140;
  const labelOffsetY = 100;
  const labelX = crossingX + labelOffsetX;
  const labelY = crossingY + labelOffsetY;

  // Label fade in animation
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_FADE_START, BEATS.LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelScale = interpolate(
    frame,
    [BEATS.LABEL_FADE_START, BEATS.LABEL_FADE_END],
    [0.8, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.5)),
    }
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
            opacity: 1,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          }}
        >
          The Economics of Code
        </div>
      )}

      {/* Chart with zoom animation */}
      <CodeCostChart />

      {/* Crossing point marker with pulse effects */}
      <WeAreHereMarker x={crossingX} y={crossingY} />

      {/* Animated arrow pointing to crossing point */}
      <AnimatedArrow
        labelX={labelX}
        labelY={labelY}
        targetX={crossingX}
        targetY={crossingY}
      />

      {/* "We are here." label */}
      {frame >= BEATS.LABEL_FADE_START && (
        <div
          style={{
            position: "absolute",
            left: labelX,
            top: labelY,
            transform: `translate(-50%, -50%) scale(${labelScale})`,
            opacity: labelOpacity,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 700,
            color: COLORS.MARKER,
            textShadow: `0 0 25px ${COLORS.MARKER_GLOW}, 0 2px 10px rgba(0,0,0,0.8)`,
            whiteSpace: "nowrap",
            padding: "12px 24px",
            backgroundColor: "rgba(26, 26, 46, 0.85)",
            borderRadius: 10,
            border: `2px solid ${COLORS.MARKER_GLOW}`,
            boxShadow: `0 0 30px ${COLORS.MARKER_GLOW}40`,
          }}
        >
          We are here.
        </div>
      )}

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 270,
          right: 60,
          opacity: 1,
          backgroundColor: "rgba(26, 26, 46, 0.85)",
          padding: "16px 20px",
          borderRadius: 8,
          border: "1px solid rgba(255, 255, 255, 0.15)",
        }}
      >
        {/* Cost to Generate */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 12,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 36,
              height: 4,
              backgroundColor: COLORS.LINE_GENERATE,
              marginRight: 12,
              borderRadius: 2,
            }}
          />
          Cost to Generate
        </div>
        {/* Patch (small CB) */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 12,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: "rgba(255, 255, 255, 0.5)",
          }}
        >
          <div
            style={{
              width: 36,
              height: 4,
              backgroundColor: COLORS.LINE_PATCH,
              marginRight: 12,
              borderRadius: 2,
              opacity: 0.35,
            }}
          />
          Patch (small codebase)
        </div>
        {/* Patch (large CB) */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 12,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 36,
              height: 4,
              backgroundColor: COLORS.LINE_PATCH,
              marginRight: 12,
              borderRadius: 2,
              opacity: 0.7,
            }}
          />
          Patch (large codebase)
        </div>
        {/* True Cost with tech debt */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 36,
              height: 0,
              borderTop: `4px dashed ${COLORS.LINE_PATCH_TOTAL}`,
              marginRight: 12,
              opacity: 0.9,
            }}
          />
          True cost (with tech debt)
        </div>
      </div>

      {/* Narration text overlay - shown during hold phase */}
      {frame >= BEATS.HOLD_START + 30 && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: interpolate(
              frame,
              [BEATS.HOLD_START + 30, BEATS.HOLD_START + 60],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.75)",
            padding: "20px 40px",
            borderRadius: 12,
            maxWidth: 1100,
          }}
        >
          <p
            style={{
              fontFamily: "Georgia, serif",
              fontSize: 26,
              color: "#ffffff",
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              fontStyle: "italic",
              lineHeight: 1.5,
              margin: 0,
            }}
          >
            "But look where we are now. The cost to generate a module just
            crossed below the total cost of patching one — on any real-world
            codebase. And they're still moving apart."
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
