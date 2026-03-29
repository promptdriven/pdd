import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  AXIS_COLOR,
  LABEL_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  X_MIN,
  X_MAX,
  dataToPixelX,
  AXES_START,
  AXES_END,
} from "./constants";

const X_LABELS = [2000, 2005, 2010, 2015, 2020, 2025];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();
  const drawDuration = AXES_END - AXES_START;

  const progress = interpolate(frame - AXES_START, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Y-axis draws top-to-bottom
  const yAxisHeight = (CHART_BOTTOM - CHART_TOP) * progress;
  // X-axis draws left-to-right
  const xAxisWidth = (CHART_RIGHT - CHART_LEFT) * progress;

  // Horizontal grid lines
  const gridLines: number[] = [];
  for (let y = CHART_TOP; y <= CHART_BOTTOM; y += GRID_SPACING) {
    gridLines.push(y);
  }

  const labelOpacity = interpolate(
    frame - AXES_START,
    [drawDuration * 0.5, drawDuration],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <>
      {/* Horizontal grid lines */}
      {gridLines.map((y) => (
        <div
          key={y}
          style={{
            position: "absolute",
            left: CHART_LEFT,
            top: y,
            width: xAxisWidth,
            height: 1,
            backgroundColor: GRID_COLOR,
            opacity: GRID_OPACITY * progress,
          }}
        />
      ))}

      {/* Y-axis line */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT,
          top: CHART_TOP,
          width: 1.5,
          height: yAxisHeight,
          backgroundColor: AXIS_COLOR,
        }}
      />

      {/* X-axis line */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT,
          top: CHART_BOTTOM,
          width: xAxisWidth,
          height: 1.5,
          backgroundColor: AXIS_COLOR,
        }}
      />

      {/* Y-axis label */}
      <div
        style={{
          position: "absolute",
          left: 20,
          top: CHART_TOP + (CHART_BOTTOM - CHART_TOP) / 2 - 80,
          width: 30,
          height: 200,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          transform: "rotate(-90deg)",
          transformOrigin: "center center",
          color: LABEL_COLOR,
          opacity: labelOpacity,
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          whiteSpace: "nowrap",
        }}
      >
        Cost (Developer Hours)
      </div>

      {/* X-axis labels */}
      {X_LABELS.map((year) => {
        const px = dataToPixelX(year);
        // Only show if x-axis has drawn to this point
        const yearProgress =
          (year - X_MIN) / (X_MAX - X_MIN);
        const visible = progress >= yearProgress;
        return (
          <div
            key={year}
            style={{
              position: "absolute",
              left: px - 20,
              top: CHART_BOTTOM + 12,
              width: 40,
              height: 20,
              textAlign: "center",
              color: LABEL_COLOR,
              opacity: visible ? labelOpacity : 0,
              fontFamily: "Inter, sans-serif",
              fontSize: 14,
              fontWeight: 400,
            }}
          >
            {year}
          </div>
        );
      })}

      {/* Y-axis tick marks (0.0, 0.25, 0.5, 0.75, 1.0) */}
      {[0, 0.25, 0.5, 0.75, 1.0].map((val) => {
        const py =
          CHART_BOTTOM -
          (val / 1.0) * (CHART_BOTTOM - CHART_TOP);
        const tickVisible =
          yAxisHeight >= CHART_BOTTOM - py;
        return (
          <div
            key={val}
            style={{
              position: "absolute",
              left: CHART_LEFT - 45,
              top: py - 8,
              width: 40,
              height: 16,
              textAlign: "right",
              color: LABEL_COLOR,
              opacity: tickVisible ? labelOpacity : 0,
              fontFamily: "Inter, sans-serif",
              fontSize: 12,
              fontWeight: 400,
            }}
          >
            {val.toFixed(2)}
          </div>
        );
      })}
    </>
  );
};

export default ChartAxes;
