import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHART_TOP,
  CHART_BOTTOM,
  MARKER_LINE_COLOR,
  LABEL_COLOR,
  BLUE_LINE_COLOR,
  DATE_MARKERS,
  GENERATE_COST_DATA,
  X_MIN,
  X_MAX,
  dataToPixelX,
  dataToPixelY,
  interpolateY,
  BLUE_LINE_START,
  BLUE_LINE_END,
} from "./constants";

export const DateMarkersOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Blue line draws from BLUE_LINE_START to BLUE_LINE_END (frame 45 to 300)
  // Determine how far the blue line has drawn (in terms of x-year)
  const blueProgress = interpolate(
    frame,
    [BLUE_LINE_START, BLUE_LINE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const currentYear = X_MIN + blueProgress * (X_MAX - X_MIN);

  return (
    <>
      {DATE_MARKERS.map((marker) => {
        const px = dataToPixelX(marker.year);

        // Marker appears when the blue line reaches its year
        const markerVisible = currentYear >= marker.year;
        const fadeIn = interpolate(
          currentYear - marker.year,
          [0, 0.5],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        if (!markerVisible) return null;

        // Y position of the blue line at this year
        const yVal = interpolateY(GENERATE_COST_DATA, marker.year);
        const py = dataToPixelY(yVal);

        return (
          <React.Fragment key={marker.label}>
            {/* Vertical dashed line */}
            <svg
              width={1920}
              height={1080}
              style={{
                position: "absolute",
                left: 0,
                top: 0,
                pointerEvents: "none",
              }}
            >
              <line
                x1={px}
                y1={CHART_TOP}
                x2={px}
                y2={CHART_BOTTOM}
                stroke={MARKER_LINE_COLOR}
                strokeWidth={1}
                strokeDasharray="4 4"
                opacity={fadeIn * 0.5}
              />
              {/* Dot on the blue line */}
              <circle
                cx={px}
                cy={py}
                r={5}
                fill={BLUE_LINE_COLOR}
                opacity={fadeIn}
              />
            </svg>

            {/* Label above */}
            <div
              style={{
                position: "absolute",
                left: px - 35,
                top: CHART_TOP - 28,
                width: 70,
                height: 24,
                textAlign: "center",
                color: LABEL_COLOR,
                opacity: fadeIn * 0.8,
                fontFamily: "Inter, sans-serif",
                fontSize: 12,
                fontWeight: 400,
                whiteSpace: "nowrap",
              }}
            >
              {marker.label}
            </div>
          </React.Fragment>
        );
      })}
    </>
  );
};

export default DateMarkersOverlay;
