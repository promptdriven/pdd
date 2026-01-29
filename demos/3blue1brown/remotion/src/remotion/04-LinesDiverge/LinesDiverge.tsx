import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { YearCounter } from "./YearCounter";
import { ShadedRegion } from "./ShadedRegion";
import { GapIndicator } from "./GapIndicator";
import {
  COLORS,
  CHART_DATA,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  CROSSING_POINT,
  BEATS,
  YEAR_COUNTER,
  LinesDivergePropsType,
} from "./constants";

export const LinesDiverge: React.FC<LinesDivergePropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

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

  // Threshold marker fades to 50% opacity
  const thresholdOpacity = interpolate(
    frame,
    [BEATS.THRESHOLD_FADE_START, BEATS.THRESHOLD_FADE_END],
    [1, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Calculate current animated year
  const currentYear = interpolate(
    frame,
    [BEATS.TIME_PROGRESS_START, BEATS.TIME_PROGRESS_END],
    [YEAR_COUNTER.startYear, YEAR_COUNTER.endYear],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Zoom out effect
  const zoomScale = interpolate(
    frame,
    [BEATS.ZOOM_OUT_START, BEATS.ZOOM_OUT_END],
    [1, 0.95],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Build path for Cost to Buy line (frozen up to 1963)
  const frozenBuyPath = CHART_DATA.costToBuyUntil1963
    .map((d, i) => {
      const x = getXPosition(d.year);
      const y = getYPosition(d.hours);
      return `${i === 0 ? "M" : "L"} ${x} ${y}`;
    })
    .join(" ");

  // Build animated path from 1963 to current year
  const getAnimatedBuyPath = () => {
    const data = CHART_DATA.costToBuyFrom1963;
    let path = `M ${getXPosition(1963)} ${getYPosition(0.5)}`;

    for (const point of data) {
      if (point.year > 1963 && point.year <= currentYear) {
        path += ` L ${getXPosition(point.year)} ${getYPosition(point.hours)}`;
      }
    }

    // Add interpolated point for current year if between data points
    if (currentYear > 1963 && currentYear < 2020) {
      for (let i = 0; i < data.length - 1; i++) {
        if (currentYear > data[i].year && currentYear < data[i + 1].year) {
          const t = (currentYear - data[i].year) / (data[i + 1].year - data[i].year);
          const interpolatedHours = data[i].hours + t * (data[i + 1].hours - data[i].hours);
          path += ` L ${getXPosition(currentYear)} ${getYPosition(interpolatedHours)}`;
          break;
        }
      }
    } else if (currentYear >= 2020) {
      path += ` L ${getXPosition(2020)} ${getYPosition(0.03)}`;
    }

    return path;
  };

  // Repair line path (static)
  const repairLinePath = `M ${getXPosition(1920)} ${getYPosition(0.5)} L ${getXPosition(2020)} ${getYPosition(0.5)}`;

  // Crossing point position
  const crossingX = getXPosition(CROSSING_POINT.year);
  const crossingY = getYPosition(CROSSING_POINT.hours);

  const yearTicks = [1920, 1930, 1940, 1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020];
  const hourTicks = [0, 0.5, 1, 1.5];

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
      <div
        style={{
          width: "100%",
          height: "100%",
          transform: `scale(${zoomScale})`,
          transformOrigin: "center center",
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
            The Economics of Sock Repair
          </div>
        )}

        {/* Year counter */}
        <YearCounter />

        {/* Chart grid and axes */}
        <svg
          width={width}
          height={height}
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          {/* Horizontal grid lines */}
          {hourTicks.map((hour) => (
            <line
              key={`h-grid-${hour}`}
              x1={CHART_MARGINS.left}
              y1={getYPosition(hour)}
              x2={width - CHART_MARGINS.right}
              y2={getYPosition(hour)}
              stroke={COLORS.GRID}
              strokeWidth={1}
              strokeDasharray="5,5"
              opacity={0.5}
            />
          ))}

          {/* Vertical grid lines */}
          {yearTicks.map((year) => (
            <line
              key={`v-grid-${year}`}
              x1={getXPosition(year)}
              y1={CHART_MARGINS.top}
              x2={getXPosition(year)}
              y2={height - CHART_MARGINS.bottom}
              stroke={COLORS.GRID}
              strokeWidth={1}
              strokeDasharray="5,5"
              opacity={0.5}
            />
          ))}

          {/* X-axis */}
          <line
            x1={CHART_MARGINS.left}
            y1={height - CHART_MARGINS.bottom}
            x2={width - CHART_MARGINS.right}
            y2={height - CHART_MARGINS.bottom}
            stroke={COLORS.AXIS}
            strokeWidth={2}
          />

          {/* Y-axis */}
          <line
            x1={CHART_MARGINS.left}
            y1={CHART_MARGINS.top}
            x2={CHART_MARGINS.left}
            y2={height - CHART_MARGINS.bottom}
            stroke={COLORS.AXIS}
            strokeWidth={2}
          />

          {/* Cost to Repair line (static) */}
          <path
            d={repairLinePath}
            fill="none"
            stroke={COLORS.LINE_REPAIR}
            strokeWidth={4}
            strokeLinecap="round"
          />

          {/* Cost to Buy line - frozen portion (up to 1980) */}
          <path
            d={frozenBuyPath}
            fill="none"
            stroke={COLORS.LINE_BUY}
            strokeWidth={4}
            strokeLinecap="round"
            strokeLinejoin="round"
          />

          {/* Cost to Buy line - animated portion (1980 onwards) */}
          <path
            d={getAnimatedBuyPath()}
            fill="none"
            stroke={COLORS.LINE_BUY}
            strokeWidth={4}
            strokeLinecap="round"
            strokeLinejoin="round"
          />

          {/* Threshold marker (faded) */}
          <circle
            cx={crossingX}
            cy={crossingY}
            r={16}
            fill={COLORS.MARKER}
            opacity={thresholdOpacity}
          />
          <circle
            cx={crossingX}
            cy={crossingY}
            r={10}
            fill={COLORS.PULSE_GLOW}
            opacity={thresholdOpacity * 0.6}
          />
        </svg>

        {/* Year labels */}
        {yearTicks.map((year) => (
          <div
            key={`year-${year}`}
            style={{
              position: "absolute",
              left: getXPosition(year),
              top: height - CHART_MARGINS.bottom + 20,
              transform: "translateX(-50%)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              fontWeight: 500,
              color: COLORS.AXIS_LABEL,
            }}
          >
            {year}
          </div>
        ))}

        {/* Hour labels */}
        {hourTicks.map((hour) => (
          <div
            key={`hour-${hour}`}
            style={{
              position: "absolute",
              left: CHART_MARGINS.left - 15,
              top: getYPosition(hour),
              transform: "translate(-100%, -50%)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              fontWeight: 500,
              color: COLORS.AXIS_LABEL,
              textAlign: "right",
            }}
          >
            {hour}
          </div>
        ))}

        {/* Y-axis label */}
        <div
          style={{
            position: "absolute",
            left: 0,
            top: 0,
            width: 70,
            height: "100%",
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
          }}
        >
          <div
            style={{
              transform: "rotate(-90deg)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 26,
              fontWeight: 600,
              color: COLORS.AXIS_LABEL,
              whiteSpace: "nowrap",
            }}
          >
            Hours of labor to buy / repair a sock
          </div>
        </div>

        {/* X-axis label */}
        <div
          style={{
            position: "absolute",
            left: "50%",
            bottom: 25,
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 26,
            fontWeight: 600,
            color: COLORS.AXIS_LABEL,
          }}
        >
          Year
        </div>

        {/* Legend */}
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

        {/* Shaded region (irrational zone) */}
        <ShadedRegion />

        {/* Gap indicator */}
        <GapIndicator />

        {/* Narration text overlay - centered on screen */}
        {frame >= BEATS.HOLD_START && (
          <div
            style={{
              position: "absolute",
              top: "18%",
              left: "50%",
              transform: "translateX(-50%)",
              opacity: narrationOpacity,
              textAlign: "center",
              backgroundColor: "rgba(0, 0, 0, 0.75)",
              padding: "30px 50px",
              borderRadius: 12,
            }}
          >
            <p
              style={{
                fontFamily: "Georgia, serif",
                fontSize: 34,
                color: "#ffffff",
                textShadow: "0 2px 10px rgba(0,0,0,0.8)",
                fontStyle: "italic",
                maxWidth: 900,
                lineHeight: 1.5,
                margin: 0,
              }}
            >
              "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."
            </p>
          </div>
        )}
      </div>
    </AbsoluteFill>
  );
};
