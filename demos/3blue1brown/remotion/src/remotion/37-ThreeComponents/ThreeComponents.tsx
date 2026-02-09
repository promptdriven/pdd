import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  COLORS,
  BEATS,
  LAYOUT,
  VERTICES,
  EDGES,
  ThreeComponentsPropsType,
} from "./constants";

// ── Helper: hex to rgb string ───────────────────────────────────
const hexToRgb = (hex: string): string => {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return "255, 255, 255";
  return `${parseInt(result[1], 16)}, ${parseInt(result[2], 16)}, ${parseInt(result[3], 16)}`;
};

// ── Vertex Node ─────────────────────────────────────────────────
// Rounded rectangle with label, glow, and sub-label (spec: Section 6.4)
interface VertexNodeProps {
  label: string;
  sublabel: string;
  color: string;
  x: number;
  y: number;
  scale: number;
  glowIntensity: number;
  sublabelOpacity: number;
}

const VertexNode: React.FC<VertexNodeProps> = ({
  label,
  sublabel,
  color,
  x,
  y,
  scale,
  glowIntensity,
  sublabelOpacity,
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
        opacity: sublabelOpacity,
      }}
    >
      {sublabel}
    </div>
  </div>
);

// ── Triangle Edge ───────────────────────────────────────────────
// SVG gradient line between two vertices with glow and animated pulse
interface TriangleEdgeProps {
  fromX: number;
  fromY: number;
  fromColor: string;
  toX: number;
  toY: number;
  toColor: string;
  progress: number;
  glowIntensity: number;
  edgePulseOffset: number;
  gradientId: string;
  filterId: string;
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
  edgePulseOffset,
  gradientId,
  filterId,
}) => {
  const dx = toX - fromX;
  const dy = toY - fromY;
  const endX = fromX + dx * progress;
  const endY = fromY + dy * progress;

  // Animated edge pulse: energy flowing along the edge via dashoffset
  const totalLength = Math.sqrt(dx * dx + dy * dy);
  const dashLength = totalLength * 0.15;
  const gapLength = totalLength * 0.85;

  return (
    <>
      <defs>
        <linearGradient
          id={gradientId}
          gradientUnits="userSpaceOnUse"
          x1={fromX}
          y1={fromY}
          x2={toX}
          y2={toY}
        >
          <stop offset="0%" stopColor={fromColor} />
          <stop offset="100%" stopColor={toColor} />
        </linearGradient>
        <filter id={filterId}>
          <feGaussianBlur stdDeviation="4" />
        </filter>
      </defs>
      {/* Glow layer */}
      <line
        x1={fromX}
        y1={fromY}
        x2={endX}
        y2={endY}
        stroke={`url(#${gradientId})`}
        strokeWidth={6}
        opacity={0.2 * glowIntensity}
        filter={`url(#${filterId})`}
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
      {/* Energy pulse layer (visible once edge is drawn and glow active) */}
      {progress > 0.95 && glowIntensity > 0.6 && (
        <line
          x1={fromX}
          y1={fromY}
          x2={endX}
          y2={endY}
          stroke={`url(#${gradientId})`}
          strokeWidth={3}
          opacity={0.35 * glowIntensity}
          strokeDasharray={`${dashLength} ${gapLength}`}
          strokeDashoffset={-edgePulseOffset}
          filter={`url(#${filterId})`}
        />
      )}
    </>
  );
};

// ── Derivation Arrow ────────────────────────────────────────────
// Dashed line with arrowhead from edge midpoint toward centroid
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
  // Shorten path: start at 40% from midpoint, end at 80%
  const startFrac = 0.4;
  const endFrac = 0.8;
  const sx = fromX + (toX - fromX) * startFrac;
  const sy = fromY + (toY - fromY) * startFrac;
  const ex = fromX + (toX - fromX) * endFrac;
  const ey = fromY + (toY - fromY) * endFrac;

  // Arrowhead computation
  const dx = ex - sx;
  const dy = ey - sy;
  const len = Math.sqrt(dx * dx + dy * dy);
  const ux = dx / len;
  const uy = dy / len;
  const headSize = 6;
  const ax = ex - ux * headSize + uy * headSize * 0.5;
  const ay = ey - uy * headSize - ux * headSize * 0.5;
  const bx = ex - ux * headSize - uy * headSize * 0.5;
  const by = ey - uy * headSize + ux * headSize * 0.5;

  return (
    <g opacity={opacity}>
      <line
        x1={sx}
        y1={sy}
        x2={ex}
        y2={ey}
        stroke="rgba(160, 160, 160, 0.4)"
        strokeWidth={1.5}
        strokeDasharray="6 4"
      />
      <polygon
        points={`${ex},${ey} ${ax},${ay} ${bx},${by}`}
        fill="rgba(160, 160, 160, 0.4)"
      />
    </g>
  );
};

// ── Integration Formula ─────────────────────────────────────────
interface IntegrationFormulaProps {
  opacity: number;
}

const IntegrationFormula: React.FC<IntegrationFormulaProps> = ({ opacity }) => (
  <div
    style={{
      position: "absolute",
      bottom: 60,
      left: "50%",
      transform: "translateX(-50%)",
      opacity,
      textAlign: "center",
    }}
  >
    <div
      style={{
        fontSize: 24,
        color: COLORS.LABEL_WHITE,
        fontWeight: "bold",
        marginBottom: 8,
      }}
    >
      <span style={{ color: COLORS.NOZZLE_BLUE }}>Prompt</span>
      {" + "}
      <span style={{ color: COLORS.WALLS_AMBER }}>Tests</span>
      {" + "}
      <span style={{ color: COLORS.GROUNDING_GREEN }}>Grounding</span>
    </div>
    <div style={{ fontSize: 18, color: COLORS.LABEL_GRAY }}>
      encodes intent + preserves behavior + maintains style
    </div>
    <div style={{ fontSize: 20, color: COLORS.LABEL_WHITE, marginTop: 8 }}>
      = Complete Specification
    </div>
  </div>
);

// ── Main Component ──────────────────────────────────────────────
export const ThreeComponents: React.FC<ThreeComponentsPropsType> = ({
  showFormula,
}) => {
  const frame = useCurrentFrame();

  // ── Phase 1: Vertex appearance (staggered, easeOutBack with overshoot) ──
  const vertexScale = (delay: number) =>
    interpolate(
      frame,
      [delay, delay + BEATS.VERTEX_SCALE_DURATION],
      [0, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.back(1.5)),
      }
    );

  const promptScale = vertexScale(BEATS.VERTEX_PROMPT_DELAY);
  const testsScale = vertexScale(BEATS.VERTEX_TESTS_DELAY);
  const groundingScale = vertexScale(BEATS.VERTEX_GROUNDING_DELAY);

  // ── Phase 2: Edge draw progress (easeOutCubic) ──
  const edgeProgress = interpolate(
    frame,
    [BEATS.EDGES_START, BEATS.EDGES_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Phase 3: Per-vertex glow intensification (staggered, easeOutQuad) ──
  const promptGlow = interpolate(
    frame,
    [BEATS.GLOW_PROMPT_START, BEATS.GLOW_PROMPT_END],
    [0.6, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const testsGlow = interpolate(
    frame,
    [BEATS.GLOW_TESTS_START, BEATS.GLOW_TESTS_END],
    [0.6, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const groundingGlow = interpolate(
    frame,
    [BEATS.GLOW_GROUNDING_START, BEATS.GLOW_GROUNDING_END],
    [0.6, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Base glow before intensification phase (vertices glow softly from appearance)
  const baseGlow = frame < BEATS.GLOW_PROMPT_START ? 0.3 : 0;
  const effectivePromptGlow = frame >= BEATS.GLOW_PROMPT_START ? promptGlow : baseGlow;
  const effectiveTestsGlow = frame >= BEATS.GLOW_TESTS_START ? testsGlow : baseGlow;
  const effectiveGroundingGlow =
    frame >= BEATS.GLOW_GROUNDING_START ? groundingGlow : baseGlow;

  // Average glow for edges
  const avgGlow = (effectivePromptGlow + effectiveTestsGlow + effectiveGroundingGlow) / 3;

  // ── Sub-label opacity (easeOutCubic) ──
  const subLabelOpacity = interpolate(
    frame,
    [BEATS.SUBLABEL_START, BEATS.SUBLABEL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Phase 4: Center code appearance (easeOutQuad) ──
  const codeOpacity = interpolate(
    frame,
    [BEATS.CODE_START, BEATS.CODE_END],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // ── Derivation arrows opacity ──
  const arrowOpacity = interpolate(
    frame,
    [BEATS.ARROWS_START, BEATS.ARROWS_END],
    [0, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // ── Integration formula opacity (easeOutCubic) ──
  const formulaOpacity = interpolate(
    frame,
    [BEATS.FORMULA_START, BEATS.FORMULA_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Edge pulse animation (continuous energy flowing along edges) ──
  // Cycles through full edge length every ~90 frames (3s) for subtle flow effect
  const edgePulseOffset = (frame % 90) / 90;

  // ── Compute edge midpoints for derivation arrows ──
  const edgeMidpoints = EDGES.map(([fromKey, toKey]) => {
    const from = VERTICES[fromKey];
    const to = VERTICES[toKey];
    return { x: (from.x + to.x) / 2, y: (from.y + to.y) / 2 };
  });

  const centroid = LAYOUT.CENTROID;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Triangle edges (SVG) */}
      <svg
        style={{
          position: "absolute",
          width: "100%",
          height: "100%",
          pointerEvents: "none",
        }}
      >
        {EDGES.map(([fromKey, toKey], i) => {
          const from = VERTICES[fromKey];
          const to = VERTICES[toKey];
          const totalLen = Math.sqrt(
            (to.x - from.x) ** 2 + (to.y - from.y) ** 2
          );
          return (
            <TriangleEdge
              key={`edge-${fromKey}-${toKey}`}
              fromX={from.x}
              fromY={from.y}
              fromColor={from.color}
              toX={to.x}
              toY={to.y}
              toColor={to.color}
              progress={edgeProgress}
              glowIntensity={avgGlow}
              edgePulseOffset={edgePulseOffset * totalLen + i * totalLen * 0.33}
              gradientId={`edgeGrad-${i}`}
              filterId={`edgeBlur-${i}`}
            />
          );
        })}

        {/* Derivation arrows from edge midpoints toward centroid */}
        {edgeMidpoints.map((mid, i) => (
          <DerivationArrow
            key={`arrow-${i}`}
            fromX={mid.x}
            fromY={mid.y}
            toX={centroid.x}
            toY={centroid.y}
            opacity={arrowOpacity}
          />
        ))}
      </svg>

      {/* Vertex nodes */}
      <VertexNode
        label={VERTICES.prompt.label}
        sublabel={VERTICES.prompt.sublabel}
        color={VERTICES.prompt.color}
        x={VERTICES.prompt.x}
        y={VERTICES.prompt.y}
        scale={promptScale}
        glowIntensity={effectivePromptGlow}
        sublabelOpacity={subLabelOpacity}
      />
      <VertexNode
        label={VERTICES.tests.label}
        sublabel={VERTICES.tests.sublabel}
        color={VERTICES.tests.color}
        x={VERTICES.tests.x}
        y={VERTICES.tests.y}
        scale={testsScale}
        glowIntensity={effectiveTestsGlow}
        sublabelOpacity={subLabelOpacity}
      />
      <VertexNode
        label={VERTICES.grounding.label}
        sublabel={VERTICES.grounding.sublabel}
        color={VERTICES.grounding.color}
        x={VERTICES.grounding.x}
        y={VERTICES.grounding.y}
        scale={groundingScale}
        glowIntensity={effectiveGroundingGlow}
        sublabelOpacity={subLabelOpacity}
      />

      {/* Center code block (NO GLOW -- spec critical) */}
      <div
        style={{
          position: "absolute",
          left: centroid.x - 80,
          top: centroid.y - 30,
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

      {/* Integration formula (standalone only) */}
      {showFormula && <IntegrationFormula opacity={formulaOpacity} />}
    </AbsoluteFill>
  );
};
