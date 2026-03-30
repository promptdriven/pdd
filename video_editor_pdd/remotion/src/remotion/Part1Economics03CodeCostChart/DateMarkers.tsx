import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  MARKER_LINE_COLOR,
  AXIS_LABEL_COLOR,
  GENERATE_COST_DATA,
  DATE_MARKERS,
  X_MIN,
  X_MAX,
  BLUE_LINE_START,
  BLUE_LINE_END,
  mapX,
  mapY,
  DataPoint,
} from "./constants";

// Interpolate Y value for a given X from the data series
function interpolateY(data: DataPoint[], xVal: number): number {
  for (let i = 0; i < data.length - 1; i++) {
    if (xVal >= data[i].x && xVal <= data[i + 1].x) {
      const t = (xVal - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
}

export const DateMarkers: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {DATE_MARKERS.map((marker) => {
        const x = mapX(marker.year);
        const yVal = interpolateY(GENERATE_COST_DATA, marker.year);
        const dotY = mapY(yVal);

        // Marker appears when the blue line reaches its year
        const lineProgress = (marker.year - X_MIN) / (X_MAX - X_MIN);
        // Blue line draws from BLUE_LINE_START to BLUE_LINE_END
        const markerAppearFrame =
          BLUE_LINE_START + lineProgress * (BLUE_LINE_END - BLUE_LINE_START);

        const markerOpacity = interpolate(
          frame,
          [markerAppearFrame, markerAppearFrame + 20],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        if (markerOpacity <= 0) return null;

        return (
          <g key={marker.label} opacity={markerOpacity}>
            {/* Vertical dashed line */}
            <line
              x1={x}
              y1={CHART_TOP}
              x2={x}
              y2={CHART_BOTTOM}
              stroke={MARKER_LINE_COLOR}
              strokeWidth={1}
              strokeDasharray="6 4"
              opacity={0.5}
            />
            {/* Label above chart */}
            <text
              x={x}
              y={CHART_TOP - 12}
              fill={AXIS_LABEL_COLOR}
              opacity={0.8}
              fontSize={12}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              textAnchor="middle"
            >
              {marker.label}
            </text>
            {/* Dot on blue line */}
            <circle cx={x} cy={dotY} r={4} fill="#4A90D9" opacity={0.9} />
          </g>
        );
      })}
    </svg>
  );
};

export default DateMarkers;
