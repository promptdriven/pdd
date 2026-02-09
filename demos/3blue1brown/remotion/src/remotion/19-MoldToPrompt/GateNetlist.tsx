import React from "react";
import { useCurrentFrame, interpolate, Easing, interpolateColors } from "remotion";
import { BEATS, COLORS, NETLIST_BLOCK, NETLIST_GATES, CODE_LINES } from "./constants";

/**
 * Renders gate-level netlist that morphs into software code lines.
 * LEFT side (setup): Teal-colored gate symbols from chip design context.
 * Morph: Gates stretch into horizontal code lines, move to RIGHT side.
 * RIGHT side (final): Gray monospace software code (no glow).
 */

// Gate symbol component
const GateSymbol: React.FC<{
  type: string;
  x: number;
  y: number;
  color: string;
  opacity: number;
}> = ({ type, x, y, color, opacity }) => {
  const w = 40;
  const h = 28;

  const label =
    type === "AND"
      ? "&"
      : type === "OR"
        ? "≥1"
        : type === "NOT"
          ? "1"
          : type === "NAND"
            ? "&"
            : type === "NOR"
              ? "≥1"
              : "?";

  const hasNegation = type === "NOT" || type === "NAND" || type === "NOR";

  return (
    <g opacity={opacity}>
      <rect
        x={x}
        y={y}
        width={w}
        height={h}
        rx={4}
        fill="none"
        stroke={color}
        strokeWidth={1.5}
      />
      <text
        x={x + w / 2}
        y={y + h / 2 + 5}
        textAnchor="middle"
        fill={color}
        fontSize={12}
        fontFamily="'JetBrains Mono', monospace"
      >
        {label}
      </text>
      {hasNegation && (
        <circle
          cx={x + w + 5}
          cy={y + h / 2}
          r={4}
          fill="none"
          stroke={color}
          strokeWidth={1.5}
        />
      )}
    </g>
  );
};

export const GateNetlist: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph progress
  const morphProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Interpolate shape dimensions (LEFT → RIGHT)
  const x = interpolate(morphProgress, [0, 1], [NETLIST_BLOCK.initialX, NETLIST_BLOCK.finalX]);
  const y = interpolate(morphProgress, [0, 1], [NETLIST_BLOCK.initialY, NETLIST_BLOCK.finalY]);
  const width = interpolate(morphProgress, [0, 1], [NETLIST_BLOCK.initialWidth, NETLIST_BLOCK.finalWidth]);
  const height = interpolate(morphProgress, [0, 1], [NETLIST_BLOCK.initialHeight, NETLIST_BLOCK.finalHeight]);

  // Background color: teal netlist → dark code background
  const colorProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const bgColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.NETLIST_BG, COLORS.CODE_BG_DARK]
  );

  const borderColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.NETLIST_BORDER, "rgba(255, 255, 255, 0.1)"]
  );

  // Gate symbols visibility (fade out during morph)
  const gatesOpacity = interpolate(
    morphProgress,
    [0, 0.4],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Code line bars visibility (fade in during morph, then out for text)
  const lineBarsOpacity = interpolate(
    morphProgress,
    [0.3, 0.7, 1],
    [0, 1, 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Code text readability (labels phase)
  const textOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Line color transitions from teal to gray
  const lineColor = interpolateColors(
    colorProgress,
    [0, 1],
    [COLORS.NETLIST_TEAL, COLORS.CODE_GRAY]
  );

  return (
    <>
      {/* Background container */}
      <rect
        x={x}
        y={y}
        width={width}
        height={height}
        rx={6}
        fill={bgColor}
        stroke={borderColor}
        strokeWidth={1}
      />

      {/* Gate symbols (visible during setup, LEFT side) */}
      {gatesOpacity > 0 && (
        <g>
          {NETLIST_GATES.map((gate, i) => (
            <GateSymbol
              key={`gate-${i}`}
              type={gate.type}
              x={x + gate.x}
              y={y + gate.y}
              color={COLORS.NETLIST_TEAL}
              opacity={gatesOpacity}
            />
          ))}
          {/* Wire connections between gates */}
          {NETLIST_GATES.slice(0, -1).map((gate, i) => {
            const nextGate = NETLIST_GATES[i + 1];
            if (!nextGate) return null;
            return (
              <line
                key={`wire-${i}`}
                x1={x + gate.x + 40}
                y1={y + gate.y + 14}
                x2={x + nextGate.x}
                y2={y + nextGate.y + 14}
                stroke={COLORS.NETLIST_TEAL}
                strokeWidth={1}
                opacity={gatesOpacity * 0.6}
              />
            );
          })}
        </g>
      )}

      {/* Horizontal line bars representing code structure (morph phase) */}
      {lineBarsOpacity > 0 && (
        <g opacity={lineBarsOpacity}>
          {CODE_LINES.map((codeLine, i) => {
            const lineY = y + 25 + i * 28;
            const lineWidth = (codeLine.length / 40) * (width - 40);
            return (
              <rect
                key={`bar-${i}`}
                x={x + 20}
                y={lineY}
                width={lineWidth}
                height={4}
                rx={2}
                fill={lineColor}
                opacity={0.8}
              />
            );
          })}
        </g>
      )}

      {/* Actual code text (fades in during labels phase, RIGHT side) */}
      {textOpacity > 0 && (
        <g opacity={textOpacity}>
          {CODE_LINES.map((line, i) => {
            const lineY = y + 32 + i * 28;
            // Stagger each line
            const lineDelay = i * 5;
            const lineOpacity = interpolate(
              frame,
              [BEATS.LABELS_START + lineDelay, BEATS.LABELS_START + 50 + lineDelay],
              [0, 1],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
                easing: Easing.out(Easing.cubic),
              }
            );

            return (
              <text
                key={`code-${i}`}
                x={x + 20}
                y={lineY}
                fontSize={14}
                fontFamily="'JetBrains Mono', 'Fira Code', 'Courier New', monospace"
                fontWeight={400}
                fill={COLORS.CODE_GRAY}
                opacity={lineOpacity}
              >
                {line}
              </text>
            );
          })}
        </g>
      )}
    </>
  );
};
