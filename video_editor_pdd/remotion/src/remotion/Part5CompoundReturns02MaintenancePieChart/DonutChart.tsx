import React from "react";
import { useCurrentFrame, Easing, interpolate } from "remotion";
import {
  CENTER_X,
  CENTER_Y,
  OUTER_RADIUS,
  INNER_RADIUS,
  BLUE,
  AMBER,
  BORDER_COLOR,
  TEXT_MUTED,
  RING_FADE_START,
  RING_FADE_DURATION,
  BLUE_SEG_START,
  BLUE_SEG_DRAW_DURATION,
  AMBER_SEG_START,
  AMBER_SEG_DRAW_DURATION,
  DEV_ANGLE_DEG,
} from "./constants";

// ── Helpers ─────────────────────────────────────────────────────────

/** Convert degrees to radians, with 0° at 12 o'clock (top). */
const deg2rad = (deg: number) => ((deg - 90) * Math.PI) / 180;

/** Describe an SVG arc path for a donut segment. */
function describeArc(
  cx: number,
  cy: number,
  outerR: number,
  innerR: number,
  startDeg: number,
  endDeg: number
): string {
  const startOuter = deg2rad(startDeg);
  const endOuter = deg2rad(endDeg);
  const startInner = deg2rad(endDeg);
  const endInner = deg2rad(startDeg);

  const largeArc = endDeg - startDeg > 180 ? 1 : 0;

  const x1 = cx + outerR * Math.cos(startOuter);
  const y1 = cy + outerR * Math.sin(startOuter);
  const x2 = cx + outerR * Math.cos(endOuter);
  const y2 = cy + outerR * Math.sin(endOuter);
  const x3 = cx + innerR * Math.cos(startInner);
  const y3 = cy + innerR * Math.sin(startInner);
  const x4 = cx + innerR * Math.cos(endInner);
  const y4 = cy + innerR * Math.sin(endInner);

  return [
    `M ${x1} ${y1}`,
    `A ${outerR} ${outerR} 0 ${largeArc} 1 ${x2} ${y2}`,
    `L ${x3} ${y3}`,
    `A ${innerR} ${innerR} 0 ${largeArc} 0 ${x4} ${y4}`,
    "Z",
  ].join(" ");
}

/** Calculate label position on the midpoint of a segment arc. */
function labelPosition(
  cx: number,
  cy: number,
  r: number,
  startDeg: number,
  endDeg: number
) {
  const midDeg = (startDeg + endDeg) / 2;
  const rad = deg2rad(midDeg);
  return { x: cx + r * Math.cos(rad), y: cy + r * Math.sin(rad) };
}

// ── Component ───────────────────────────────────────────────────────

export const DonutChart: React.FC = () => {
  const frame = useCurrentFrame();

  // 1) Ring outline fade-in (frame 0-20)
  const ringOpacity = interpolate(
    frame,
    [RING_FADE_START, RING_FADE_START + RING_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // 2) Center text fade-in (same timing as ring)
  const centerTextOpacity = interpolate(
    frame,
    [RING_FADE_START, RING_FADE_START + RING_FADE_DURATION],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // 3) Blue segment draw (frame 30-60)
  const blueProgress = interpolate(
    frame,
    [BLUE_SEG_START, BLUE_SEG_START + BLUE_SEG_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.bezier(0.42, 0, 0.58, 1) }
  );

  // 4) Amber segment draw (frame 60-150)
  const amberProgress = interpolate(
    frame,
    [AMBER_SEG_START, AMBER_SEG_START + AMBER_SEG_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.bezier(0.42, 0, 0.58, 1) }
  );

  // Blue label/value opacity
  const blueLabelOpacity = interpolate(
    frame,
    [BLUE_SEG_START + BLUE_SEG_DRAW_DURATION - 10, BLUE_SEG_START + BLUE_SEG_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Amber label/value opacity
  const amberLabelOpacity = interpolate(
    frame,
    [AMBER_SEG_START + AMBER_SEG_DRAW_DURATION - 15, AMBER_SEG_START + AMBER_SEG_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Amber value emphasis scale (easeOut back)
  const amberValueScale = interpolate(
    frame,
    [AMBER_SEG_START + AMBER_SEG_DRAW_DURATION - 15, AMBER_SEG_START + AMBER_SEG_DRAW_DURATION],
    [0.6, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.3)),
    }
  );

  // Segment angles
  const blueEndAngle = blueProgress * DEV_ANGLE_DEG;
  const amberEndAngle = DEV_ANGLE_DEG + amberProgress * (360 - DEV_ANGLE_DEG);

  // Label positions — outside the donut
  const labelRadius = OUTER_RADIUS + 60;
  const blueLabelPos = labelPosition(CENTER_X, CENTER_Y, labelRadius, 0, DEV_ANGLE_DEG);
  const amberLabelPos = labelPosition(CENTER_X, CENTER_Y, labelRadius, DEV_ANGLE_DEG, 360);

  // Leader line anchor on donut edge
  const blueAnchor = labelPosition(CENTER_X, CENTER_Y, OUTER_RADIUS + 5, 0, DEV_ANGLE_DEG);
  const amberAnchor = labelPosition(CENTER_X, CENTER_Y, OUTER_RADIUS + 5, DEV_ANGLE_DEG, 360);

  const midRadius = (OUTER_RADIUS + INNER_RADIUS) / 2;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Empty donut ring outline */}
      <circle
        cx={CENTER_X}
        cy={CENTER_Y}
        r={midRadius}
        fill="none"
        stroke={BORDER_COLOR}
        strokeWidth={OUTER_RADIUS - INNER_RADIUS}
        opacity={ringOpacity * 0.3}
      />

      {/* Inner and outer circle borders */}
      <circle
        cx={CENTER_X}
        cy={CENTER_Y}
        r={OUTER_RADIUS}
        fill="none"
        stroke={BORDER_COLOR}
        strokeWidth={2}
        opacity={ringOpacity}
      />
      <circle
        cx={CENTER_X}
        cy={CENTER_Y}
        r={INNER_RADIUS}
        fill="none"
        stroke={BORDER_COLOR}
        strokeWidth={2}
        opacity={ringOpacity}
      />

      {/* Center text */}
      <text
        x={CENTER_X}
        y={CENTER_Y - 8}
        textAnchor="middle"
        fill={TEXT_MUTED}
        opacity={centerTextOpacity}
        fontSize={11}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        letterSpacing={3}
      >
        SOFTWARE
      </text>
      <text
        x={CENTER_X}
        y={CENTER_Y + 12}
        textAnchor="middle"
        fill={TEXT_MUTED}
        opacity={centerTextOpacity}
        fontSize={11}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        letterSpacing={3}
      >
        COST
      </text>

      {/* Blue segment — Initial Development */}
      {blueProgress > 0 && (
        <path
          d={describeArc(CENTER_X, CENTER_Y, OUTER_RADIUS, INNER_RADIUS, 0, blueEndAngle)}
          fill={BLUE}
          stroke={BORDER_COLOR}
          strokeWidth={2}
        />
      )}

      {/* Amber segment — Maintenance */}
      {amberProgress > 0 && (
        <path
          d={describeArc(
            CENTER_X,
            CENTER_Y,
            OUTER_RADIUS,
            INNER_RADIUS,
            DEV_ANGLE_DEG,
            amberEndAngle
          )}
          fill={AMBER}
          stroke={BORDER_COLOR}
          strokeWidth={2}
        />
      )}

      {/* Blue label + leader line */}
      {blueLabelOpacity > 0 && (
        <g opacity={blueLabelOpacity}>
          <line
            x1={blueAnchor.x}
            y1={blueAnchor.y}
            x2={blueLabelPos.x}
            y2={blueLabelPos.y}
            stroke={BLUE}
            strokeWidth={1}
            opacity={0.5}
          />
          <text
            x={blueLabelPos.x}
            y={blueLabelPos.y - 12}
            textAnchor="middle"
            fill={BLUE}
            opacity={0.7}
            fontSize={14}
            fontFamily="Inter, sans-serif"
          >
            Initial Development
          </text>
          <text
            x={blueLabelPos.x}
            y={blueLabelPos.y + 10}
            textAnchor="middle"
            fill={BLUE}
            fontSize={20}
            fontFamily="Inter, sans-serif"
            fontWeight={700}
          >
            10-20%
          </text>
        </g>
      )}

      {/* Amber label + leader line */}
      {amberLabelOpacity > 0 && (
        <g opacity={amberLabelOpacity}>
          <line
            x1={amberAnchor.x}
            y1={amberAnchor.y}
            x2={amberLabelPos.x}
            y2={amberLabelPos.y}
            stroke={AMBER}
            strokeWidth={1}
            opacity={0.5}
          />
          <text
            x={amberLabelPos.x}
            y={amberLabelPos.y - 16}
            textAnchor="middle"
            fill={AMBER}
            opacity={0.7}
            fontSize={14}
            fontFamily="Inter, sans-serif"
          >
            Maintenance
          </text>
          <text
            x={amberLabelPos.x}
            y={amberLabelPos.y + 12}
            textAnchor="middle"
            fill={AMBER}
            fontSize={28}
            fontFamily="Inter, sans-serif"
            fontWeight={700}
            style={{
              transform: `scale(${amberValueScale})`,
              transformOrigin: `${amberLabelPos.x}px ${amberLabelPos.y + 12}px`,
            }}
          >
            80-90%
          </text>
        </g>
      )}
    </svg>
  );
};

export default DonutChart;
