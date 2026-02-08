import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TRIANGLE, ThreeComponentsPropsType } from "./constants";

// ── Helper: hex to rgb string ───────────────────────────────────
const hexToRgb = (hex: string): string => {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return "255, 255, 255";
  return `${parseInt(result[1], 16)}, ${parseInt(result[2], 16)}, ${parseInt(result[3], 16)}`;
};

// ── Vertex Node ─────────────────────────────────────────────────
interface VertexNodeProps {
  label: string;
  subLabel: string;
  color: string;
  x: number;
  y: number;
  scale: number;
  glowIntensity: number;
  subLabelOpacity: number;
}

const VertexNode: React.FC<VertexNodeProps> = ({
  label,
  subLabel,
  color,
  x,
  y,
  scale,
  glowIntensity,
  subLabelOpacity,
}) => (
  <div
    style={{
      position: "absolute",
      left: x,
      top: y,
      transform: `translate(-50%, -50%) scale(${scale})`,
      textAlign: "center",
    }}
  >
    <div
      style={{
        backgroundColor: `rgba(${hexToRgb(color)}, 0.15)`,
        border: `2px solid ${color}`,
        borderRadius: 12,
        padding: "14px 24px",
        boxShadow: `0 0 ${30 * glowIntensity}px ${color}`,
        minWidth: 140,
      }}
    >
      <span
        style={{
          fontSize: 20,
          fontWeight: "bold",
          color: color,
          letterSpacing: 2,
        }}
      >
        {label}
      </span>
    </div>
    <div
      style={{
        marginTop: 10,
        fontSize: 15,
        color: "rgba(255, 255, 255, 0.6)",
        fontStyle: "italic",
        opacity: subLabelOpacity,
      }}
    >
      {subLabel}
    </div>
  </div>
);

// ── Triangle Edge (SVG) ─────────────────────────────────────────
interface TriangleEdgeProps {
  fromX: number;
  fromY: number;
  fromColor: string;
  toX: number;
  toY: number;
  toColor: string;
  progress: number;
  glowIntensity: number;
  gradientId: string;
}

const TriangleEdge: React.FC<TriangleEdgeProps> = ({
  fromX,
  fromY,
  fromColor,
  toX,
  toY,
  toColor,
  progress,
  glowIntensity,
  gradientId,
}) => {
  const dx = toX - fromX;
  const dy = toY - fromY;
  const endX = fromX + dx * progress;
  const endY = fromY + dy * progress;

  return (
    <>
      <defs>
        <linearGradient id={gradientId} x1={fromX} y1={fromY} x2={toX} y2={toY} gradientUnits="userSpaceOnUse">
          <stop offset="0%" stopColor={fromColor} />
          <stop offset="100%" stopColor={toColor} />
        </linearGradient>
      </defs>
      {/* Glow layer */}
      <line
        x1={fromX}
        y1={fromY}
        x2={endX}
        y2={endY}
        stroke={fromColor}
        strokeWidth={6}
        opacity={0.2 * glowIntensity}
        filter="url(#edgeBlur)"
      />
      {/* Main line */}
      <line
        x1={fromX}
        y1={fromY}
        x2={endX}
        y2={endY}
        stroke={`url(#${gradientId})`}
        strokeWidth={2}
        opacity={0.8}
      />
    </>
  );
};

// ── Derivation Arrow (dashed, pointing inward) ─────────────────
interface DerivationArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  opacity: number;
}

const DerivationArrow: React.FC<DerivationArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  opacity,
}) => {
  // Shorten the arrow: start 40% from edge midpoint, end 80% toward centroid
  const startX = fromX + (toX - fromX) * 0.4;
  const startY = fromY + (toY - fromY) * 0.4;
  const endX = fromX + (toX - fromX) * 0.8;
  const endY = fromY + (toY - fromY) * 0.8;

  return (
    <line
      x1={startX}
      y1={startY}
      x2={endX}
      y2={endY}
      stroke="rgba(160, 160, 160, 0.4)"
      strokeWidth={1.5}
      strokeDasharray="6 4"
      opacity={opacity}
    />
  );
};

// ── Main Component ──────────────────────────────────────────────
export const ThreeComponents: React.FC<ThreeComponentsPropsType> = () => {
  const frame = useCurrentFrame();

  // Vertex positions
  const vertices = [
    { label: "PROMPT", subLabel: "encodes intent", color: COLORS.NOZZLE_BLUE, ...TRIANGLE.PROMPT, delay: BEATS.VERTEX_PROMPT_START },
    { label: "TESTS", subLabel: "preserves behavior", color: COLORS.WALLS_AMBER, ...TRIANGLE.TESTS, delay: BEATS.VERTEX_TESTS_START },
    { label: "GROUNDING", subLabel: "maintains style", color: COLORS.GROUNDING_GREEN, ...TRIANGLE.GROUNDING, delay: BEATS.VERTEX_GROUNDING_START },
  ];

  // Vertex appearance (staggered scale-up with overshoot)
  const vertexScale = (delay: number) =>
    interpolate(
      frame,
      [delay, delay + 30],
      [0, 1],
      { extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.5)) }
    );

  // Edge draw progress
  const edgeProgress = interpolate(
    frame,
    [BEATS.EDGES_START, BEATS.EDGES_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Glow intensification
  const glowPulse = interpolate(
    frame,
    [BEATS.GLOW_INTENSIFY_START, BEATS.GLOW_INTENSIFY_END],
    [0.6, 1.0],
    { extrapolateRight: "clamp" }
  );

  // Sub-label opacity
  const subLabelOpacity = interpolate(
    frame,
    [BEATS.SUBLABEL_START, BEATS.SUBLABEL_END],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Center code appearance
  const codeOpacity = interpolate(
    frame,
    [BEATS.CODE_START, BEATS.CODE_END],
    [0, 0.5],
    { extrapolateRight: "clamp" }
  );

  // Derivation arrows
  const arrowOpacity = interpolate(
    frame,
    [BEATS.ARROWS_START, BEATS.ARROWS_END],
    [0, 0.3],
    { extrapolateRight: "clamp" }
  );

  // Edge midpoints for derivation arrows
  const edgeMidpoints = [
    { x: (TRIANGLE.PROMPT.x + TRIANGLE.TESTS.x) / 2, y: (TRIANGLE.PROMPT.y + TRIANGLE.TESTS.y) / 2 },
    { x: (TRIANGLE.TESTS.x + TRIANGLE.GROUNDING.x) / 2, y: (TRIANGLE.TESTS.y + TRIANGLE.GROUNDING.y) / 2 },
    { x: (TRIANGLE.GROUNDING.x + TRIANGLE.PROMPT.x) / 2, y: (TRIANGLE.GROUNDING.y + TRIANGLE.PROMPT.y) / 2 },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* SVG layer for edges and arrows */}
      <svg
        style={{
          position: "absolute",
          width: "100%",
          height: "100%",
          top: 0,
          left: 0,
        }}
      >
        <defs>
          <filter id="edgeBlur">
            <feGaussianBlur stdDeviation="4" />
          </filter>
        </defs>

        {/* Triangle edges */}
        <TriangleEdge
          fromX={TRIANGLE.PROMPT.x}
          fromY={TRIANGLE.PROMPT.y}
          fromColor={COLORS.NOZZLE_BLUE}
          toX={TRIANGLE.TESTS.x}
          toY={TRIANGLE.TESTS.y}
          toColor={COLORS.WALLS_AMBER}
          progress={edgeProgress}
          glowIntensity={glowPulse}
          gradientId="edge-prompt-tests"
        />
        <TriangleEdge
          fromX={TRIANGLE.TESTS.x}
          fromY={TRIANGLE.TESTS.y}
          fromColor={COLORS.WALLS_AMBER}
          toX={TRIANGLE.GROUNDING.x}
          toY={TRIANGLE.GROUNDING.y}
          toColor={COLORS.GROUNDING_GREEN}
          progress={edgeProgress}
          glowIntensity={glowPulse}
          gradientId="edge-tests-grounding"
        />
        <TriangleEdge
          fromX={TRIANGLE.GROUNDING.x}
          fromY={TRIANGLE.GROUNDING.y}
          fromColor={COLORS.GROUNDING_GREEN}
          toX={TRIANGLE.PROMPT.x}
          toY={TRIANGLE.PROMPT.y}
          toColor={COLORS.NOZZLE_BLUE}
          progress={edgeProgress}
          glowIntensity={glowPulse}
          gradientId="edge-grounding-prompt"
        />

        {/* Derivation arrows pointing to centroid */}
        {edgeMidpoints.map((mid, i) => (
          <DerivationArrow
            key={i}
            fromX={mid.x}
            fromY={mid.y}
            toX={TRIANGLE.CENTROID.x}
            toY={TRIANGLE.CENTROID.y}
            opacity={arrowOpacity}
          />
        ))}
      </svg>

      {/* Vertex nodes */}
      {vertices.map((v) => (
        <VertexNode
          key={v.label}
          label={v.label}
          subLabel={v.subLabel}
          color={v.color}
          x={v.x}
          y={v.y}
          scale={vertexScale(v.delay)}
          glowIntensity={glowPulse}
          subLabelOpacity={subLabelOpacity}
        />
      ))}

      {/* Center code block (NO GLOW) */}
      <div
        style={{
          position: "absolute",
          left: TRIANGLE.CENTROID.x - 80,
          top: TRIANGLE.CENTROID.y - 30,
          width: 160,
          textAlign: "center",
          opacity: codeOpacity,
        }}
      >
        <div
          style={{
            backgroundColor: "rgba(160, 160, 160, 0.1)",
            border: "1px solid rgba(160, 160, 160, 0.25)",
            borderRadius: 8,
            padding: "12px 16px",
            fontFamily: "monospace",
            fontSize: 13,
            color: "rgba(160, 160, 160, 0.6)",
          }}
        >
          Generated Code
        </div>
      </div>
    </AbsoluteFill>
  );
};
