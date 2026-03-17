import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { CircuitGrid } from "./CircuitGrid";
import { HandDrawnSchematic } from "./HandDrawnSchematic";
import { VerilogCodeBlock } from "./VerilogCodeBlock";
import { CompilerIcon } from "./CompilerIcon";
import { FlowArrow } from "./FlowArrow";
import { GateNetlist } from "./GateNetlist";
import { EquivalenceOverlay } from "./EquivalenceOverlay";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  UI_FONT,
  UI_FONT_SIZE,
  SAME_INPUT_COLOR,
  SAME_INPUT_OPACITY,
  // Phase 1 layout
  CODE_X,
  CODE_Y,
  CODE_W,
  CODE_H,
  CODE_FONT_SIZE,
  COMPILER_X,
  COMPILER_Y,
  COMPILER_SIZE,
  NETLIST_X,
  NETLIST_Y,
  NETLIST_W,
  NETLIST_H,
  // Phase 2 layout
  PHASE2_CODE_Y,
  PHASE2_CODE_W,
  PHASE2_CODE_H,
  PHASE2_CODE_FONT_SIZE,
  SAME_INPUT_Y,
  COL_1_X,
  COL_2_X,
  COL_3_X,
  PHASE2_NETLIST_Y,
  PHASE2_NETLIST_W,
  PHASE2_NETLIST_H,
  // Phase 1 timing
  CODE_TYPING_START,
  CODE_CHAR_DELAY,
  ARROW_DRAW_START,
  ARROW_DRAW_END,
  COMPILER_APPEAR_START,
  COMPILER_APPEAR_END,
  SINGLE_NETLIST_DRAW_START,
  SINGLE_NETLIST_DRAW_END,
  // Phase 2 timing
  PHASE2_START,
  PHASE2_CROSSFADE_END,
  TRIPLE_ARROW_START,
  TRIPLE_ARROW_END,
  TRIPLE_NETLIST_START,
  TRIPLE_NETLIST_END,
} from "./constants";

export const defaultPart2ParadigmShift07VerilogSynthesisTripleProps = {};

const COLUMNS = [COL_1_X, COL_2_X, COL_3_X];

export const Part2ParadigmShift07VerilogSynthesisTriple: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase transition: Phase 1 fades out, Phase 2 fades in
  const phase1Opacity = interpolate(
    frame,
    [PHASE2_START, PHASE2_CROSSFADE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  const phase2Opacity = interpolate(
    frame,
    [PHASE2_START, PHASE2_CROSSFADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // "Same input" label fade
  const sameInputOpacity = interpolate(
    frame,
    [PHASE2_START + 20, PHASE2_CROSSFADE_END],
    [0, SAME_INPUT_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Circuit board grid background */}
      <CircuitGrid />

      {/* ============ PHASE 1: Schematic → Verilog → Single netlist ============ */}
      {phase1Opacity > 0 && (
        <AbsoluteFill style={{ opacity: phase1Opacity }}>
          {/* Dissolving hand-drawn schematic */}
          <HandDrawnSchematic />

          {/* Verilog code block with typing effect */}
          <VerilogCodeBlock
            x={CODE_X}
            y={CODE_Y}
            width={CODE_W}
            height={CODE_H}
            fontSize={CODE_FONT_SIZE}
            typeEffect
            charDelay={CODE_CHAR_DELAY}
            typeStartFrame={CODE_TYPING_START}
          />

          {/* Arrow from code to compiler */}
          <FlowArrow
            fromX={CODE_X}
            fromY={CODE_Y + CODE_H / 2 + 10}
            toX={COMPILER_X}
            toY={COMPILER_Y - COMPILER_SIZE / 2 - 10}
            drawStart={ARROW_DRAW_START}
            drawEnd={ARROW_DRAW_END}
          />

          {/* Compiler icon */}
          <CompilerIcon
            x={COMPILER_X}
            y={COMPILER_Y}
            size={COMPILER_SIZE}
            appearStart={COMPILER_APPEAR_START}
            appearEnd={COMPILER_APPEAR_END}
            pulse
          />

          {/* Arrow from compiler to netlist */}
          <FlowArrow
            fromX={COMPILER_X}
            fromY={COMPILER_Y + COMPILER_SIZE / 2 + 20}
            toX={NETLIST_X}
            toY={NETLIST_Y - NETLIST_H / 2}
            drawStart={ARROW_DRAW_START + 15}
            drawEnd={ARROW_DRAW_END + 15}
          />

          {/* Single gate-level netlist */}
          <GateNetlist
            x={NETLIST_X}
            y={NETLIST_Y}
            width={NETLIST_W}
            height={NETLIST_H}
            layoutIndex={0}
            drawStart={SINGLE_NETLIST_DRAW_START}
            drawDuration={SINGLE_NETLIST_DRAW_END - SINGLE_NETLIST_DRAW_START}
          />
        </AbsoluteFill>
      )}

      {/* ============ PHASE 2: Triple synthesis ============ */}
      {phase2Opacity > 0 && (
        <AbsoluteFill style={{ opacity: phase2Opacity }}>
          {/* "Same input" label */}
          <div
            style={{
              position: "absolute",
              left: 0,
              top: SAME_INPUT_Y,
              width: CANVAS_WIDTH,
              textAlign: "center",
              fontFamily: UI_FONT,
              fontSize: UI_FONT_SIZE,
              color: SAME_INPUT_COLOR,
              opacity: sameInputOpacity,
              letterSpacing: "2px",
              textTransform: "uppercase",
              pointerEvents: "none",
            }}
          >
            Same input
          </div>

          {/* Shared Verilog code at top */}
          <VerilogCodeBlock
            x={CANVAS_WIDTH / 2}
            y={PHASE2_CODE_Y}
            width={PHASE2_CODE_W}
            height={PHASE2_CODE_H}
            fontSize={PHASE2_CODE_FONT_SIZE}
          />

          {/* Three arrows down to columns */}
          {COLUMNS.map((cx, i) => (
            <FlowArrow
              key={`triple-arrow-${i}`}
              fromX={cx}
              fromY={PHASE2_CODE_Y + PHASE2_CODE_H / 2 + 10}
              toX={cx}
              toY={PHASE2_NETLIST_Y - PHASE2_NETLIST_H / 2 - 40}
              drawStart={TRIPLE_ARROW_START + i * 5}
              drawEnd={TRIPLE_ARROW_END + i * 5}
            />
          ))}

          {/* Three small compiler icons at arrow midpoints */}
          {COLUMNS.map((cx, i) => {
            const midY =
              (PHASE2_CODE_Y + PHASE2_CODE_H / 2 + 10 + PHASE2_NETLIST_Y - PHASE2_NETLIST_H / 2 - 40) / 2;
            return (
              <CompilerIcon
                key={`compiler-${i}`}
                x={cx}
                y={midY}
                size={40}
                appearStart={TRIPLE_ARROW_START + i * 5}
                appearEnd={TRIPLE_ARROW_START + i * 5 + 20}
                pulse
              />
            );
          })}

          {/* Three different netlists */}
          {COLUMNS.map((cx, i) => (
            <GateNetlist
              key={`netlist-${i}`}
              x={cx}
              y={PHASE2_NETLIST_Y}
              width={PHASE2_NETLIST_W}
              height={PHASE2_NETLIST_H}
              layoutIndex={i}
              drawStart={TRIPLE_NETLIST_START + i * 10}
              drawDuration={TRIPLE_NETLIST_END - TRIPLE_NETLIST_START}
            />
          ))}

          {/* Netlist labels showing different gate counts */}
          {COLUMNS.map((cx, i) => {
            const labels = ["6 gates", "8 gates", "5 gates"];
            const labelOpacity = interpolate(
              frame,
              [TRIPLE_NETLIST_END - 20, TRIPLE_NETLIST_END],
              [0, 0.4],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );
            return (
              <div
                key={`label-${i}`}
                style={{
                  position: "absolute",
                  left: cx - 50,
                  top: PHASE2_NETLIST_Y + PHASE2_NETLIST_H / 2 + 8,
                  width: 100,
                  textAlign: "center",
                  fontFamily: UI_FONT,
                  fontSize: 10,
                  color: SAME_INPUT_COLOR,
                  opacity: labelOpacity,
                  pointerEvents: "none",
                }}
              >
                {labels[i]}
              </div>
            );
          })}

          {/* Equivalence checkmarks + label + dashed line */}
          <EquivalenceOverlay />
        </AbsoluteFill>
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift07VerilogSynthesisTriple;
