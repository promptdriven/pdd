import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  SEGMENT_STROKE_COLOR,
  MAINTENANCE_COLOR,
  DEVELOPMENT_COLOR,
  CHART_CX,
  CHART_CY,
  CHART_RADIUS,
  CHART_STROKE_WIDTH,
  MAINTENANCE_DEGREES,
  DEVELOPMENT_DEGREES,
  MAINTENANCE_LABEL_X,
  MAINTENANCE_LABEL_Y,
  DEVELOPMENT_LABEL_X,
  DEVELOPMENT_LABEL_Y,
  STAT_Y_START,
  STAT_Y_GAP,
  OUTLINE_START,
  OUTLINE_DURATION,
  MAINTENANCE_FILL_START,
  MAINTENANCE_FILL_DURATION,
  DEVELOPMENT_FILL_START,
  DEVELOPMENT_FILL_DURATION,
  LABELS_START,
  LABELS_FADE_DURATION,
  STAT1_START,
  STAT2_START,
  PULSE_START,
  PULSE_END,
  MORPH_START,
  MORPH_DURATION,
  FONT_FAMILY,
  COUNTER_FONT_SIZE,
  COUNTER_FONT_WEIGHT,
} from "./constants";
import { PieSegment, getSegmentMidpoint } from "./PieSegment";
import { ConnectorLabel } from "./ConnectorLabel";
import { StatCallout } from "./StatCallout";

export const defaultPart5CompoundReturns02MaintenancePieChartProps = {};

/**
 * Animated pie chart showing 80-90% of software cost goes to maintenance.
 * 480 frames @ 30fps = 16 seconds.
 */
export const Part5CompoundReturns02MaintenancePieChart: React.FC = () => {
  const frame = useCurrentFrame();

  // === Outline circle draw animation (frames 0-30) ===
  const outlineProgress = interpolate(
    frame,
    [OUTLINE_START, OUTLINE_START + OUTLINE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Circle circumference for stroke-dasharray animation
  const circumference = 2 * Math.PI * CHART_RADIUS;
  const strokeDashoffset = circumference * (1 - outlineProgress);

  // === Animated percentage counter for maintenance ===
  const counterValue = interpolate(
    frame,
    [MAINTENANCE_FILL_START, MAINTENANCE_FILL_START + MAINTENANCE_FILL_DURATION],
    [0, 85],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const counterDisplay =
    counterValue >= 84 ? "80-90%" : `${Math.round(counterValue)}%`;

  // Counter opacity
  const counterOpacity = interpolate(
    frame,
    [MAINTENANCE_FILL_START, MAINTENANCE_FILL_START + 10],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // === Development percentage text ===
  const devTextOpacity = interpolate(
    frame,
    [DEVELOPMENT_FILL_START + 10, DEVELOPMENT_FILL_START + DEVELOPMENT_FILL_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // === Morph progress (frames 420-480) ===
  const morphProgress = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Connector line start points (on the edge of the pie at each segment midpoint)
  const maintMid = getSegmentMidpoint(
    CHART_CX,
    CHART_CY,
    CHART_RADIUS + 10,
    0,
    MAINTENANCE_DEGREES
  );
  const devMid = getSegmentMidpoint(
    CHART_CX,
    CHART_CY,
    CHART_RADIUS + 10,
    MAINTENANCE_DEGREES,
    MAINTENANCE_DEGREES + DEVELOPMENT_DEGREES
  );

  // Overall fade-out during morph
  const contentOpacity = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* SVG Glow filter */}
        <defs>
          <filter id="segmentGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="12" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* === Outline circle (draws in from top, clockwise) === */}
        <circle
          cx={CHART_CX}
          cy={CHART_CY}
          r={CHART_RADIUS}
          fill="none"
          stroke={SEGMENT_STROKE_COLOR}
          strokeWidth={CHART_STROKE_WIDTH}
          strokeDasharray={circumference}
          strokeDashoffset={strokeDashoffset}
          transform={`rotate(-90, ${CHART_CX}, ${CHART_CY})`}
        />

        {/* === Maintenance Segment (amber, 0° to 306°) === */}
        <PieSegment
          cx={CHART_CX}
          cy={CHART_CY}
          radius={CHART_RADIUS}
          startAngleDeg={0}
          endAngleDeg={MAINTENANCE_DEGREES}
          color={MAINTENANCE_COLOR}
          strokeColor={SEGMENT_STROKE_COLOR}
          strokeWidth={CHART_STROKE_WIDTH}
          fillStartFrame={MAINTENANCE_FILL_START}
          fillDuration={MAINTENANCE_FILL_DURATION}
          glowColor={MAINTENANCE_COLOR}
          pulseAmplitude={0.015}
          pulseStartFrame={PULSE_START}
          pulseEndFrame={PULSE_END}
          morphProgress={morphProgress}
        />

        {/* === Development Segment (blue, 306° to 360°) === */}
        <PieSegment
          cx={CHART_CX}
          cy={CHART_CY}
          radius={CHART_RADIUS}
          startAngleDeg={MAINTENANCE_DEGREES}
          endAngleDeg={MAINTENANCE_DEGREES + DEVELOPMENT_DEGREES}
          color={DEVELOPMENT_COLOR}
          strokeColor={SEGMENT_STROKE_COLOR}
          strokeWidth={CHART_STROKE_WIDTH}
          fillStartFrame={DEVELOPMENT_FILL_START}
          fillDuration={DEVELOPMENT_FILL_DURATION}
          morphProgress={morphProgress}
        />

        {/* === Center percentage counter (maintenance) === */}
        {counterOpacity > 0 && (
          <text
            x={CHART_CX}
            y={CHART_CY - 10}
            fontFamily={FONT_FAMILY}
            fontSize={COUNTER_FONT_SIZE}
            fontWeight={COUNTER_FONT_WEIGHT}
            fill={MAINTENANCE_COLOR}
            textAnchor="middle"
            dominantBaseline="middle"
            opacity={counterOpacity * contentOpacity}
          >
            {counterDisplay}
          </text>
        )}

        {/* === Small "Maintenance" label below counter === */}
        {counterOpacity > 0 && (
          <text
            x={CHART_CX}
            y={CHART_CY + 20}
            fontFamily={FONT_FAMILY}
            fontSize={14}
            fontWeight={500}
            fill={MAINTENANCE_COLOR}
            textAnchor="middle"
            dominantBaseline="middle"
            opacity={counterOpacity * 0.7 * contentOpacity}
          >
            Maintenance
          </text>
        )}

        {/* === Development percentage inside/near its sliver === */}
        {devTextOpacity > 0 && (
          <text
            x={CHART_CX + CHART_RADIUS + 40}
            y={CHART_CY - CHART_RADIUS * 0.3}
            fontFamily={FONT_FAMILY}
            fontSize={18}
            fontWeight={COUNTER_FONT_WEIGHT}
            fill={DEVELOPMENT_COLOR}
            textAnchor="start"
            dominantBaseline="middle"
            opacity={devTextOpacity * contentOpacity}
          >
            10-20%
          </text>
        )}

        {/* === Connector labels === */}
        <g opacity={contentOpacity}>
          <ConnectorLabel
            text="Maintenance: 80-90%"
            color={MAINTENANCE_COLOR}
            labelX={MAINTENANCE_LABEL_X}
            labelY={MAINTENANCE_LABEL_Y}
            connectorFromX={maintMid.x}
            connectorFromY={maintMid.y}
            fadeStartFrame={LABELS_START}
            fadeDuration={LABELS_FADE_DURATION}
          />
          <ConnectorLabel
            text="Initial Development: 10-20%"
            color={DEVELOPMENT_COLOR}
            labelX={DEVELOPMENT_LABEL_X}
            labelY={DEVELOPMENT_LABEL_Y}
            connectorFromX={devMid.x}
            connectorFromY={devMid.y}
            fadeStartFrame={LABELS_START}
            fadeDuration={LABELS_FADE_DURATION}
          />
        </g>

        {/* === Statistic callouts === */}
        <g opacity={contentOpacity}>
          <StatCallout
            text="McKinsey: 40% more on maintenance with high tech debt"
            x={CHART_CX}
            y={STAT_Y_START}
            fadeStartFrame={STAT1_START}
          />
          <StatCallout
            text="Stripe: 1/3 of dev week lost to debt"
            x={CHART_CX}
            y={STAT_Y_START + STAT_Y_GAP}
            fadeStartFrame={STAT2_START}
          />
        </g>

        {/* === Morph to exponential curve hint (frames 420-480) === */}
        {morphProgress > 0 && (
          <g opacity={morphProgress}>
            {/* A horizontal baseline that the pie "flattens" into */}
            <line
              x1={CHART_CX - 300}
              y1={CHART_CY + 200}
              x2={CHART_CX + 300}
              y2={CHART_CY + 200}
              stroke={MAINTENANCE_COLOR}
              strokeWidth={2}
              opacity={morphProgress * 0.8}
            />
            {/* Rising curve hint */}
            <path
              d={`M ${CHART_CX - 300} ${CHART_CY + 200} Q ${CHART_CX} ${CHART_CY + 200 - morphProgress * 150} ${CHART_CX + 300} ${CHART_CY + 200 - morphProgress * 300}`}
              fill="none"
              stroke={MAINTENANCE_COLOR}
              strokeWidth={3}
              opacity={morphProgress * 0.6}
            />
          </g>
        )}
      </svg>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns02MaintenancePieChart;
