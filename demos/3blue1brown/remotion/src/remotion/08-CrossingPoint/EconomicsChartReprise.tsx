import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";
import { CodeCostChart } from "./CodeCostChart";
import {
  COLORS,
  CROSSING_POINT_2,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  PULSE_CONFIG,
} from "./constants";

/**
 * Reprise timing configuration.
 *
 * The Visual 7 window in Part 5 spans ~244 frames (76.38s-84.5s at 30fps).
 * The original spec assumed 750 frames (25s), so all timings are compressed
 * proportionally to fit the narration-synced window.
 *
 * Narration beats (local frames at 30fps):
 *   0   - "But the economics changed..."       (segment [20] at 76.4s)
 *   120 - "behavior that was rational becomes..." (segment [21] at 80.4s)
 *   222 - "darning socks."                      (segment [22] at 83.8s)
 */
const REPRISE_BEATS = {
  // Cross-dissolve fade-in
  FADE_IN_START: 0,
  FADE_IN_END: 45,

  // Pulse cycle 1: assertive, 7 rings (synced with "economics changed")
  PULSE_CYCLE_1_START: 10,
  PULSE_CYCLE_1_RINGS: 7,
  PULSE_CYCLE_1_RING_STAGGER: 8,
  PULSE_CYCLE_1_RING_DURATION: 30,
  PULSE_CYCLE_1_MAX_RADIUS: 80,

  // Pulse cycle 2: reinforcing, 7 rings (synced with "when economics change")
  PULSE_CYCLE_2_START: 90,
  PULSE_CYCLE_2_RINGS: 7,
  PULSE_CYCLE_2_RING_STAGGER: 8,
  PULSE_CYCLE_2_RING_DURATION: 30,
  PULSE_CYCLE_2_MAX_RADIUS: 90,

  // Pulse cycle 3: gentle wind-down, 4 rings (synced with "becomes...")
  PULSE_CYCLE_3_START: 160,
  PULSE_CYCLE_3_RINGS: 4,
  PULSE_CYCLE_3_RING_STAGGER: 10,
  PULSE_CYCLE_3_RING_DURATION: 25,
  PULSE_CYCLE_3_MAX_RADIUS: 60,

  // "...darning socks." text fade-in (synced with segment [22])
  DARNING_TEXT_FADE_START: 200,
  DARNING_TEXT_FADE_END: 230,

  // Hold: stillness for the statement to land
  HOLD_START: 230,
};

/**
 * EconomicsChartReprise -- "This is a REPRISE, not a repeat."
 *
 * A wrapper composition for the economics chart that adds reprise-specific
 * enhancements over the base Part 1 CrossingPoint:
 *
 * - Chart shown immediately at full view (no zoom animation)
 * - Chart simplified: fork lines and annotations dimmed
 * - Three-pulse-cycle structure with emotional arc (assertive -> reinforcing -> gentle)
 * - "...darning socks." text overlay as the visual punchline
 * - Cross-dissolve fade-in from previous visual
 * - Final hold with no animation for stillness
 *
 * Spec: 05-compound-returns/09_economics_chart_reprise.md
 */
export const EconomicsChartReprise: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Coordinate helpers (same as CrossingPoint.tsx)
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

  // Crossing point 2 position in pixels
  const crossingX = getXPosition(CROSSING_POINT_2.year);
  const crossingY = getYPosition(CROSSING_POINT_2.hours);

  // ── Cross-dissolve fade-in ────────────────────────────────────────
  const chartOpacity = interpolate(
    frame,
    [REPRISE_BEATS.FADE_IN_START, REPRISE_BEATS.FADE_IN_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── "We are here." label (shown immediately, no fade-in) ──────────
  const labelOffsetX = 140;
  const labelOffsetY = 100;
  const labelX = crossingX + labelOffsetX;
  const labelY = crossingY + labelOffsetY;

  // ── "...darning socks." text ──────────────────────────────────────
  const darningTextOpacity = interpolate(
    frame,
    [REPRISE_BEATS.DARNING_TEXT_FADE_START, REPRISE_BEATS.DARNING_TEXT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Enhanced pulse ring helper ────────────────────────────────────
  const renderPulseCycle = (
    cycleKey: string,
    cycleStart: number,
    ringCount: number,
    ringStagger: number,
    ringDuration: number,
    maxRadius: number,
  ) => {
    const markerRadius = PULSE_CONFIG.MARKER_RADIUS;
    const rings: React.ReactNode[] = [];

    for (let i = 0; i < ringCount; i++) {
      const ringStartFrame = cycleStart + i * ringStagger;
      const ringEndFrame = ringStartFrame + ringDuration;

      if (frame < ringStartFrame || frame > ringEndFrame) {
        continue;
      }

      const progress = (frame - ringStartFrame) / ringDuration;

      // Ring expands from marker radius to maxRadius
      const radius = interpolate(
        progress,
        [0, 1],
        [markerRadius, maxRadius],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );

      // Opacity: fade in, peak, fade out with easeOutQuad feel
      const opacity = interpolate(
        progress,
        [0, 0.15, 0.5, 1],
        [0, 0.7 - i * 0.07, 0.4 - i * 0.05, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );

      // Color transitions from blue to white as ring expands
      const whiteBlend = interpolate(progress, [0, 0.6, 1], [0, 0.3, 0.8], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });

      rings.push(
        <circle
          key={`${cycleKey}-ring-${i}`}
          cx={crossingX}
          cy={crossingY}
          r={radius}
          fill="none"
          stroke={whiteBlend > 0.5 ? "#ffffff" : COLORS.PULSE_GLOW}
          strokeWidth={Math.max(1, 3 - i * 0.3)}
          opacity={opacity}
        />
      );
    }

    return rings;
  };

  // ── Marker glow pulsation ─────────────────────────────────────────
  const glowIntensity = 8 + 4 * Math.sin(frame * 0.12);
  const markerRadius = PULSE_CONFIG.MARKER_RADIUS;

  // During hold phase, stop all pulsing for stillness
  const isHoldPhase = frame >= REPRISE_BEATS.HOLD_START;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
        opacity: chartOpacity,
      }}
    >
      {/* Title */}
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

      {/* Chart with dimmed fork lines for reprise simplification */}
      <CodeCostChart
        startAtFullView={true}
        forkSmallOpacity={0.2}
        forkLargeOpacity={0.3}
        totalCostOpacity={1}
        techDebtAreaOpacity={0.2}
        baselineOpacity={0.4}
      />

      {/* Crossing point marker and enhanced pulse rings (SVG layer) */}
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          {/* Blue radial gradient for pulse rings */}
          <radialGradient id="reprisePulseGradient" cx="50%" cy="50%" r="50%">
            <stop offset="0%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.9" />
            <stop offset="40%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0.4" />
            <stop offset="100%" stopColor={COLORS.PULSE_GLOW} stopOpacity="0" />
          </radialGradient>

          {/* Marker glow filter */}
          <filter id="repriseMarkerGlow" x="-200%" y="-200%" width="500%" height="500%">
            <feGaussianBlur in="SourceGraphic" stdDeviation={glowIntensity} result="blur" />
            <feColorMatrix
              in="blur"
              type="matrix"
              values="0.29 0 0 0 0
                      0.56 0 0 0 0
                      0.85 0 0 0 0
                      0 0 0 1 0"
              result="blueBlur"
            />
            <feMerge>
              <feMergeNode in="blueBlur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Enhanced pulse cycle 1: assertive (7 rings) */}
        {!isHoldPhase &&
          renderPulseCycle(
            "cycle1",
            REPRISE_BEATS.PULSE_CYCLE_1_START,
            REPRISE_BEATS.PULSE_CYCLE_1_RINGS,
            REPRISE_BEATS.PULSE_CYCLE_1_RING_STAGGER,
            REPRISE_BEATS.PULSE_CYCLE_1_RING_DURATION,
            REPRISE_BEATS.PULSE_CYCLE_1_MAX_RADIUS,
          )}

        {/* Enhanced pulse cycle 2: reinforcing (7 rings, slightly larger) */}
        {!isHoldPhase &&
          renderPulseCycle(
            "cycle2",
            REPRISE_BEATS.PULSE_CYCLE_2_START,
            REPRISE_BEATS.PULSE_CYCLE_2_RINGS,
            REPRISE_BEATS.PULSE_CYCLE_2_RING_STAGGER,
            REPRISE_BEATS.PULSE_CYCLE_2_RING_DURATION,
            REPRISE_BEATS.PULSE_CYCLE_2_MAX_RADIUS,
          )}

        {/* Enhanced pulse cycle 3: gentle wind-down (4 rings, smaller) */}
        {!isHoldPhase &&
          renderPulseCycle(
            "cycle3",
            REPRISE_BEATS.PULSE_CYCLE_3_START,
            REPRISE_BEATS.PULSE_CYCLE_3_RINGS,
            REPRISE_BEATS.PULSE_CYCLE_3_RING_STAGGER,
            REPRISE_BEATS.PULSE_CYCLE_3_RING_DURATION,
            REPRISE_BEATS.PULSE_CYCLE_3_MAX_RADIUS,
          )}

        {/* Outer glow ring (always visible once faded in) */}
        <circle
          cx={crossingX}
          cy={crossingY}
          r={markerRadius * 1.3}
          fill="none"
          stroke={COLORS.MARKER_GLOW}
          strokeWidth={4}
          opacity={0.4}
        />

        {/* Main white marker with blue glow */}
        <circle
          cx={crossingX}
          cy={crossingY}
          r={markerRadius}
          fill={COLORS.MARKER}
          filter="url(#repriseMarkerGlow)"
        />

        {/* Inner blue accent */}
        <circle
          cx={crossingX}
          cy={crossingY}
          r={markerRadius - 8}
          fill={COLORS.MARKER_GLOW}
          opacity={0.5}
        />
      </svg>

      {/* Arrow from label to crossing point */}
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          <filter id="repriseArrowGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="3" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>
        {(() => {
          const dx = crossingX - labelX;
          const dy = crossingY - labelY;
          const distance = Math.sqrt(dx * dx + dy * dy);
          const nx = dx / distance;
          const ny = dy / distance;
          const startX = labelX + nx * 60;
          const startY = labelY + ny * 30;
          const endX = crossingX - nx * 35;
          const endY = crossingY - ny * 35;
          const angle = Math.atan2(endY - startY, endX - startX);
          const arrowHeadLength = 15;
          const arrowHeadAngle = Math.PI / 6;
          return (
            <>
              <line
                x1={startX}
                y1={startY}
                x2={endX}
                y2={endY}
                stroke={COLORS.MARKER}
                strokeWidth={3}
                opacity={1}
                filter="url(#repriseArrowGlow)"
                strokeLinecap="round"
              />
              <polygon
                points={`${endX},${endY} ${endX - arrowHeadLength * Math.cos(angle - arrowHeadAngle)},${endY - arrowHeadLength * Math.sin(angle - arrowHeadAngle)} ${endX - arrowHeadLength * Math.cos(angle + arrowHeadAngle)},${endY - arrowHeadLength * Math.sin(angle + arrowHeadAngle)}`}
                fill={COLORS.MARKER}
                opacity={1}
                filter="url(#repriseArrowGlow)"
              />
            </>
          );
        })()}
      </svg>

      {/* "We are here." label (immediately visible, no fade-in for reprise) */}
      <div
        style={{
          position: "absolute",
          left: labelX,
          top: labelY,
          transform: "translate(-50%, -50%)",
          opacity: 1,
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

      {/* "...darning socks." text -- the visual punchline */}
      {frame >= REPRISE_BEATS.DARNING_TEXT_FADE_START && (
        <div
          style={{
            position: "absolute",
            left: crossingX + 80,
            top: crossingY + 160,
            opacity: darningTextOpacity,
          }}
        >
          <span
            style={{
              color: "rgba(217, 148, 74, 0.7)",
              fontSize: 24,
              fontFamily: "Inter, system-ui, sans-serif",
              fontStyle: "italic",
              textShadow: "0 2px 8px rgba(0,0,0,0.6)",
            }}
          >
            ...darning socks.
          </span>
        </div>
      )}

      {/* Legend (simplified for reprise -- dimmer to reduce visual noise) */}
      <div
        style={{
          position: "absolute",
          top: 270,
          right: 60,
          opacity: 0.5,
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
        {/* True cost (with tech debt) */}
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
    </AbsoluteFill>
  );
};
