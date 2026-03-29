import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHIP_OUTLINE,
  CHIP_FILL_OPACITY,
  CHIP_LABEL_COLOR,
  CHIP_X,
  CHIP_Y,
  CHIP_WIDTH,
  CHIP_HEIGHT,
  CHIP_FADE_START,
  CHIP_FADE_END,
  CODE_KEYWORD,
  GATE_COLOR,
  GATE_STREAM_START,
  WIDTH,
} from "./constants";

const CHIP_FADE_DURATION = 30; // frames for chip to fade in

export const SynthesisChip: React.FC = () => {
  const frame = useCurrentFrame();

  const chipFrame = frame - CHIP_FADE_START;
  if (chipFrame < 0) return null;

  const chipOpacity = interpolate(chipFrame, [0, CHIP_FADE_DURATION], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Arrow pulse for input (before gate stream starts)
  const pulseCycle = frame % 30;
  const inputPulse = interpolate(pulseCycle, [0, 15, 30], [0.4, 1, 0.4], {
    easing: Easing.inOut(Easing.sin),
  });

  // Code symbol flow into chip (left side)
  const showInputFlow = frame >= CHIP_FADE_END && frame < GATE_STREAM_START + 120;
  // Gate symbol flow out of chip (right side)
  const showOutputFlow = frame >= GATE_STREAM_START;

  const chipLeft = CHIP_X - CHIP_WIDTH / 2;
  const chipTop = CHIP_Y - CHIP_HEIGHT / 2;

  return (
    <div style={{ position: "absolute", top: 0, left: 0, width: WIDTH, height: 1080, opacity: chipOpacity }}>
      <svg
        width={WIDTH}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Chip body */}
        <rect
          x={chipLeft}
          y={chipTop}
          width={CHIP_WIDTH}
          height={CHIP_HEIGHT}
          rx={8}
          ry={8}
          fill={CHIP_OUTLINE}
          fillOpacity={CHIP_FILL_OPACITY}
          stroke={CHIP_OUTLINE}
          strokeWidth={2}
        />

        {/* Chip pins (top) */}
        {Array.from({ length: 6 }).map((_, i) => (
          <rect
            key={`pin-t-${i}`}
            x={chipLeft + 20 + i * 28}
            y={chipTop - 12}
            width={8}
            height={12}
            fill={CHIP_OUTLINE}
            opacity={0.6}
          />
        ))}
        {/* Chip pins (bottom) */}
        {Array.from({ length: 6 }).map((_, i) => (
          <rect
            key={`pin-b-${i}`}
            x={chipLeft + 20 + i * 28}
            y={chipTop + CHIP_HEIGHT}
            width={8}
            height={12}
            fill={CHIP_OUTLINE}
            opacity={0.6}
          />
        ))}

        {/* Input arrow (left side) */}
        <line
          x1={chipLeft - 120}
          y1={CHIP_Y}
          x2={chipLeft - 4}
          y2={CHIP_Y}
          stroke={CODE_KEYWORD}
          strokeWidth={2}
          opacity={inputPulse}
          markerEnd="url(#arrowIn)"
        />
        <defs>
          <marker
            id="arrowIn"
            markerWidth={10}
            markerHeight={7}
            refX={10}
            refY={3.5}
            orient="auto"
          >
            <polygon points="0 0, 10 3.5, 0 7" fill={CODE_KEYWORD} />
          </marker>
          <marker
            id="arrowOut"
            markerWidth={10}
            markerHeight={7}
            refX={10}
            refY={3.5}
            orient="auto"
          >
            <polygon points="0 0, 10 3.5, 0 7" fill={GATE_COLOR} />
          </marker>
        </defs>

        {/* Output arrow (right side) */}
        <line
          x1={chipLeft + CHIP_WIDTH + 4}
          y1={CHIP_Y}
          x2={chipLeft + CHIP_WIDTH + 120}
          y2={CHIP_Y}
          stroke={GATE_COLOR}
          strokeWidth={2}
          opacity={showOutputFlow ? 1 : inputPulse * 0.5}
          markerEnd="url(#arrowOut)"
        />

        {/* Input code symbols flowing in */}
        {showInputFlow &&
          Array.from({ length: 5 }).map((_, i) => {
            const flowFrame = (frame - CHIP_FADE_END + i * 12) % 60;
            const fx = interpolate(flowFrame, [0, 60], [chipLeft - 200, chipLeft - 10], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            });
            const fOpacity = interpolate(flowFrame, [0, 10, 50, 60], [0, 0.9, 0.9, 0], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            });
            const symbols = ["{", "=", ";", "<=", "@"];
            return (
              <text
                key={`in-${i}`}
                x={fx}
                y={CHIP_Y + 4}
                fill={CODE_KEYWORD}
                opacity={fOpacity}
                fontSize={14}
                fontFamily="'JetBrains Mono', monospace"
                textAnchor="middle"
              >
                {symbols[i]}
              </text>
            );
          })}
      </svg>

      {/* SYNTHESIS label */}
      <div
        style={{
          position: "absolute",
          left: chipLeft,
          top: chipTop,
          width: CHIP_WIDTH,
          height: CHIP_HEIGHT,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          fontFamily: "'Inter', sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: CHIP_LABEL_COLOR,
          letterSpacing: 2,
          opacity: 0.9,
        }}
      >
        SYNTHESIS
      </div>

      {/* "Verilog" label above input arrow */}
      <div
        style={{
          position: "absolute",
          left: chipLeft - 180,
          top: CHIP_Y - 30,
          fontFamily: "'Inter', sans-serif",
          fontSize: 12,
          color: CODE_KEYWORD,
          opacity: 0.78,
          letterSpacing: 1,
        }}
      >
        VERILOG HDL
      </div>

      {/* "Gate Netlist" label above output arrow */}
      {showOutputFlow && (
        <div
          style={{
            position: "absolute",
            left: chipLeft + CHIP_WIDTH + 30,
            top: CHIP_Y - 30,
            fontFamily: "'Inter', sans-serif",
            fontSize: 12,
            color: GATE_COLOR,
            opacity: 0.78,
            letterSpacing: 1,
          }}
        >
          GATE NETLIST
        </div>
      )}
    </div>
  );
};
