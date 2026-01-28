import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { AnimatedPieSegment } from "./AnimatedPieSegment";
import {
  COLORS,
  PIE_SEGMENTS,
  BEATS,
  CHART_CENTER,
  CHART_RADIUS,
  PieChartPropsType,
} from "./constants";

// Convert degrees to radians, adjusting so 0° is at 12 o'clock
const degreesToRadians = (degrees: number) => {
  return ((degrees - 90) * Math.PI) / 180;
};

// Calculate label position at the midpoint of a segment, slightly outside
const getLabelPosition = (startAngle: number, endAngle: number, radiusOffset: number = 1.35) => {
  const midAngle = (startAngle + endAngle) / 2;
  const midRad = degreesToRadians(midAngle);
  return {
    x: CHART_CENTER.x + CHART_RADIUS * radiusOffset * Math.cos(midRad),
    y: CHART_CENTER.y + CHART_RADIUS * radiusOffset * Math.sin(midRad),
  };
};

export const PieChart: React.FC<PieChartPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();

  // Base circle outline appears (frame 60-120)
  const baseOpacity = interpolate(
    frame,
    [BEATS.BASE_APPEAR_START, BEATS.BASE_APPEAR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Title fade in with base
  const titleOpacity = interpolate(
    frame,
    [BEATS.BASE_APPEAR_START, BEATS.BASE_APPEAR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Initial Development label appears after blue segment draws
  const blueLabelOpacity = interpolate(
    frame,
    [BEATS.BLUE_SEGMENT_END - 30, BEATS.BLUE_SEGMENT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Maintenance label appears after amber segment draws
  const amberLabelOpacity = interpolate(
    frame,
    [BEATS.AMBER_SEGMENT_END - 60, BEATS.AMBER_SEGMENT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Percentages fade in (frame 300-360)
  const percentageOpacity = interpolate(
    frame,
    [BEATS.PERCENTAGES_START, BEATS.PERCENTAGES_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Label positions
  const blueLabelPos = getLabelPosition(
    PIE_SEGMENTS.initialDevelopment.startAngle,
    PIE_SEGMENTS.initialDevelopment.endAngle,
    1.5 // Further out for the small segment
  );

  const amberLabelPos = getLabelPosition(
    PIE_SEGMENTS.maintenance.startAngle,
    PIE_SEGMENTS.maintenance.endAngle,
    0.55 // Inside the large segment
  );

  return (
    <AbsoluteFill
      style={{
        background: COLORS.BACKGROUND,
      }}
    >
      {/* Title */}
      {showTitle && (
        <div
          style={{
            position: "absolute",
            top: 60,
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
          Where Software Costs Go
        </div>
      )}

      {/* Base circle outline */}
      <svg
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          opacity: baseOpacity,
        }}
      >
        <defs>
          <filter id="base-shadow" x="-50%" y="-50%" width="200%" height="200%">
            <feDropShadow
              dx="0"
              dy="4"
              stdDeviation="10"
              floodColor="rgba(0,0,0,0.3)"
            />
          </filter>
        </defs>
        <circle
          cx={CHART_CENTER.x}
          cy={CHART_CENTER.y}
          r={CHART_RADIUS}
          fill="none"
          stroke="rgba(255,255,255,0.15)"
          strokeWidth={2}
          filter="url(#base-shadow)"
        />
      </svg>

      {/* Blue segment - Initial Development (15%) */}
      <AnimatedPieSegment
        startAngle={PIE_SEGMENTS.initialDevelopment.startAngle}
        endAngle={PIE_SEGMENTS.initialDevelopment.endAngle}
        color={PIE_SEGMENTS.initialDevelopment.color}
        startFrame={BEATS.BLUE_SEGMENT_START}
        endFrame={BEATS.BLUE_SEGMENT_END}
        shouldPulse={false}
      />

      {/* Amber segment - Maintenance (85%) */}
      <AnimatedPieSegment
        startAngle={PIE_SEGMENTS.maintenance.startAngle}
        endAngle={PIE_SEGMENTS.maintenance.endAngle}
        color={PIE_SEGMENTS.maintenance.color}
        startFrame={BEATS.AMBER_SEGMENT_START}
        endFrame={BEATS.AMBER_SEGMENT_END}
        pulseStartFrame={BEATS.PULSE_START}
        shouldPulse={true}
      />

      {/* Initial Development label */}
      <div
        style={{
          position: "absolute",
          left: blueLabelPos.x,
          top: blueLabelPos.y,
          transform: "translate(-50%, -50%)",
          opacity: blueLabelOpacity,
          textAlign: "center",
        }}
      >
        <div
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 22,
            fontWeight: 500,
            color: COLORS.LABEL,
            marginBottom: 8,
            textShadow: "0 2px 8px rgba(0,0,0,0.7)",
          }}
        >
          {PIE_SEGMENTS.initialDevelopment.label}
        </div>
        <div
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 700,
            color: PIE_SEGMENTS.initialDevelopment.color,
            opacity: percentageOpacity,
            textShadow: "0 2px 8px rgba(0,0,0,0.7)",
          }}
        >
          {PIE_SEGMENTS.initialDevelopment.percentageLabel}
        </div>
      </div>

      {/* Maintenance label */}
      <div
        style={{
          position: "absolute",
          left: amberLabelPos.x,
          top: amberLabelPos.y,
          transform: "translate(-50%, -50%)",
          opacity: amberLabelOpacity,
          textAlign: "center",
        }}
      >
        <div
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 26,
            fontWeight: 500,
            color: COLORS.LABEL,
            marginBottom: 8,
            textShadow: "0 2px 8px rgba(0,0,0,0.7)",
          }}
        >
          {PIE_SEGMENTS.maintenance.label}
        </div>
        <div
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 36,
            fontWeight: 700,
            color: PIE_SEGMENTS.maintenance.color,
            opacity: percentageOpacity,
            textShadow: "0 2px 8px rgba(0,0,0,0.7)",
          }}
        >
          {PIE_SEGMENTS.maintenance.percentageLabel}
        </div>
      </div>

      {/* Connector line for the small segment's label */}
      <svg
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          pointerEvents: "none",
          opacity: blueLabelOpacity,
        }}
      >
        {(() => {
          const innerPos = getLabelPosition(
            PIE_SEGMENTS.initialDevelopment.startAngle,
            PIE_SEGMENTS.initialDevelopment.endAngle,
            1.05
          );
          const outerPos = getLabelPosition(
            PIE_SEGMENTS.initialDevelopment.startAngle,
            PIE_SEGMENTS.initialDevelopment.endAngle,
            1.35
          );
          return (
            <line
              x1={innerPos.x}
              y1={innerPos.y}
              x2={outerPos.x}
              y2={outerPos.y}
              stroke="rgba(255,255,255,0.5)"
              strokeWidth={2}
            />
          );
        })()}
      </svg>
    </AbsoluteFill>
  );
};
